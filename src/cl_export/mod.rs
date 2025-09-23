use crate::{
    ast::{
        Ast,
        ast_block::{AstStatement, StatementKind},
        ast_expr::{AstExpr, Atom, ExprKind, Op},
        ast_fn::AstFunc,
    },
    interner::SharedInterner,
    lexer::TokenKind,
    symbols::{SymbolKind, SymbolTable},
    types::{TypeArena, TypeId, TypeKind},
};
use cranelift::{
    codegen::{
        Context,
        ir::{Function, UserFuncName},
    },
    prelude::*,
};
use cranelift_codegen::{ir::FuncRef, verify_function};
use cranelift_module::{DataDescription, FuncId, Linkage, Module, ModuleResult};
use cranelift_object::{ObjectBuilder, ObjectModule, ObjectProduct};
use isa::CallConv;
use rustc_hash::FxHashMap;
use std::fs::File;
use std::path::PathBuf;
use std::{fs, io::Write};
use target_lexicon::Triple;

#[derive(Copy, Clone, Debug)]
pub enum CraneliftId {
    Func(FuncId),
    FnParam { block: Block, param_index: usize },
    Var(Variable),
}

pub struct CLExporter<'a> {
    interner: SharedInterner,
    target_triple: Triple,
    print_ir: bool,
    ast: &'a Ast,
    types: &'a TypeArena,
    symbols: &'a mut SymbolTable,
    func_defs_in_funcs: FxHashMap<FnInFn, FuncRef>,
}

#[derive(Eq, Hash, PartialEq)]
struct FnInFn {
    from: FuncId,
    calling: FuncId,
}

impl<'a> CLExporter<'a> {
    pub fn new(
        interner: SharedInterner,
        target_triple: Triple,
        print_ir: bool,
        ast: &'a Ast,
        types: &'a TypeArena,
        symbols: &'a mut SymbolTable,
    ) -> Self {
        Self {
            interner,
            target_triple,
            print_ir,
            ast,
            types,
            symbols,
            func_defs_in_funcs: FxHashMap::default(),
        }
    }

    pub fn cl_compile(&mut self) -> color_eyre::Result<()> {
        let obj_prod = self.compile()?;

        fs::create_dir_all("./lang_tmp")?;
        let output = PathBuf::from("./lang_tmp/out.o");
        let mut file = File::create(output)?;
        obj_prod.object.write_stream(&mut file).unwrap();
        Ok(())
    }
    fn compile(&mut self) -> color_eyre::Result<ObjectProduct> {
        let mut shared_builder = settings::builder();
        shared_builder.enable("is_pic")?;
        let shared_flags = settings::Flags::new(shared_builder);

        let isa_builder = isa::lookup(self.target_triple.clone())?;
        let isa = isa_builder.finish(shared_flags)?;
        let call_conv = isa.default_call_conv();

        let obj_builder =
            ObjectBuilder::new(isa, "main", cranelift_module::default_libcall_names())?;
        let mut obj_module = ObjectModule::new(obj_builder);

        for extern_fn in &self.ast.extern_fns {
            let interner_reader = self.interner.read();
            let fn_name = interner_reader.resolve(extern_fn.ident_id);
            let cl_func = self
                .parse_extern_fn(&mut obj_module, &extern_fn, fn_name)
                .expect("Failed to build extern fn into cl func id");
            let symb = self.symbols.resolve_mut(extern_fn.symbol_id);
            symb.cranelift_id = Some(CraneliftId::Func(cl_func));
        }

        for func in self.ast.fns.iter() {
            self.parse_fn(func, &mut obj_module, call_conv)?;
        }
        let res = obj_module.finish();
        Ok(res)
    }

    fn parse_extern_fn(
        &self,
        module: &mut ObjectModule,
        func: &AstFunc,
        fn_name: &str,
    ) -> ModuleResult<FuncId> {
        let mut sig = module.make_signature();
        let fn_symb = self.symbols.resolve(func.symbol_id);
        let fn_type_id = if let SymbolKind::Fn { fn_type_id, .. } = fn_symb.kind {
            fn_type_id
        } else {
            unreachable!();
        };
        let (params_t, ret_t) = match self.types.kind(fn_type_id.unwrap()) {
            TypeKind::Fn { params, ret, .. } => (params, ret),
            t => unreachable!("extern fn should have a typekind of fn: {t:?}"),
        };

        for param in params_t.iter() {
            let type_kind = self.types.kind(*param);
            let cl_type = type_kind.to_cl_type();
            sig.params.push(AbiParam::new(cl_type));
        }

        let ret_cl_type = self.types.kind(*ret_t).to_cl_type();
        sig.returns.push(AbiParam::new(ret_cl_type));

        module.declare_function(fn_name, Linkage::Import, &sig)
    }

    fn parse_fn(
        &mut self,
        ast_fn: &AstFunc,
        obj_module: &mut ObjectModule,
        call_conv: CallConv,
    ) -> color_eyre::Result<()> {
        let fn_name = {
            let reader = self.interner.read();
            // TODO: remove this to_string, it wants to hold the lock open for the entire parse_fn
            // call, this seems wasteful.
            reader.resolve(ast_fn.ident_id).to_string()
        };

        let mut sig = Signature::new(call_conv);
        let symbol = self.symbols.resolve_mut(ast_fn.symbol_id);
        let fn_type_id = if let SymbolKind::Fn { fn_type_id, .. } = symbol.kind {
            fn_type_id
        } else {
            unreachable!();
        };
        let (params_t, ret_t) = match self.types.kind(fn_type_id.unwrap()) {
            TypeKind::Fn { params, ret, .. } => (params, ret),
            t => unreachable!("extern fn should have a typekind of fn: {t:?}"),
        };
        for param_type_id in params_t {
            let cl_type = match self.types.kind(*param_type_id) {
                TypeKind::Int => types::I32,
                TypeKind::Uint => todo!(),
                TypeKind::Str => todo!(),
                TypeKind::CStr => todo!(),
                TypeKind::Ref(_) => todo!(),
                TypeKind::Unknown => todo!(),
                TypeKind::Var => todo!(),
                t => {
                    dbg!(t);
                    todo!();
                }
            };
            sig.params.push(AbiParam::new(cl_type));
        }
        let cl_type = match self.types.kind(*ret_t) {
            TypeKind::Int => types::I32,
            t => {
                dbg!(t);
                todo!();
            }
        };
        sig.returns.push(AbiParam::new(cl_type));

        let fid = obj_module.declare_function(&fn_name, Linkage::Export, &sig)?;
        symbol.cranelift_id = Some(CraneliftId::Func(fid));

        let mut func = Function::with_name_signature(UserFuncName::user(0, 0), sig);
        let mut func_ctx = FunctionBuilderContext::new();
        let mut fn_builder = FunctionBuilder::new(&mut func, &mut func_ctx);

        let block = fn_builder.create_block();
        fn_builder.switch_to_block(block);
        fn_builder.seal_block(block);
        fn_builder.append_block_params_for_function_params(block);
        for (i, arg) in ast_fn.args.iter().enumerate() {
            let symb = self.symbols.resolve_mut(arg.symbol_id);
            symb.cranelift_id = Some(CraneliftId::FnParam {
                block,
                param_index: i,
            });
        }

        let body = match &ast_fn.body {
            None => panic!("fn body was none after being parsed"),
            Some(body) => body,
        };
        for statement in &body.statements {
            self.statement_to_cl(fid, statement, &mut fn_builder, obj_module, call_conv)?;
        }

        fn_builder.seal_all_blocks();
        fn_builder.finalize();

        if self.print_ir {
            println!("{}", func.display());
            let mut ir_file = File::create("./lang_tmp/a.clif")?;
            ir_file.write_all(format!("{}", func.display()).as_bytes())?;
        }

        if self.print_ir {
            let flags = settings::Flags::new(settings::builder());
            verify_function(&func, &flags)?;
        }
        let mut context = Context::for_function(func);
        obj_module.define_function(fid, &mut context)?;
        Ok(())
    }

    fn statement_to_cl(
        &mut self,
        fid: FuncId,
        statement: &AstStatement,
        fn_builder: &mut FunctionBuilder,
        obj_module: &mut ObjectModule,
        call_conv: CallConv,
    ) -> color_eyre::Result<()> {
        match &statement.kind {
            StatementKind::Expr(expr) => {
                self.expr_to_cl(fid, expr, fn_builder, obj_module, call_conv)?;
            }
            StatementKind::ExplicitReturn(expr) => {
                let cl_val = self.expr_to_cl(fid, expr, fn_builder, obj_module, call_conv)?;
                fn_builder.ins().return_(&[cl_val]);
            }
            StatementKind::BlockReturn(expr) => {
                let cl_val = self.expr_to_cl(fid, expr, fn_builder, obj_module, call_conv)?;
                fn_builder.ins().return_(&[cl_val]);
            }
            StatementKind::Decleration {
                symbol_id,
                ident_id: _,
                ident_token_at: _,
                expr,
            } => {
                let symb = self.symbols.resolve_mut(*symbol_id);
                match symb.kind {
                    SymbolKind::Var {
                        type_id,
                        is_used: _,
                        is_mutable: _,
                    } => {
                        let ty = self.types.kind(type_id.unwrap());
                        let cl_var = match ty {
                            TypeKind::Int => fn_builder.declare_var(types::I32),
                            TypeKind::Uint => todo!(),
                            TypeKind::Str => todo!(),
                            TypeKind::CStr => todo!(),
                            TypeKind::Ref(type_id) => todo!(),
                            TypeKind::Unknown => todo!(),
                            TypeKind::Var => todo!(),
                            t => {
                                dbg!(t);
                                todo!();
                            }
                        };
                        symb.cranelift_id = Some(CraneliftId::Var(cl_var));
                        let cl_val =
                            self.expr_to_cl(fid, expr, fn_builder, obj_module, call_conv)?;
                        fn_builder.def_var(cl_var, cl_val);
                    }
                    _ => todo!(),
                };
            }
            StatementKind::Assignment {
                ident_id: _,
                ident_token_at: _,
                expr,
                symbol_id,
            } => {
                let symb = self.symbols.resolve_mut(symbol_id.unwrap());
                match symb.kind {
                    SymbolKind::Var {
                        type_id: _,
                        is_used: _,
                        is_mutable: _,
                    } => {
                        let cl_var = match symb.cranelift_id.unwrap() {
                            CraneliftId::Var(cl_var) => cl_var,
                            _ => unreachable!(),
                        };
                        symb.cranelift_id = Some(CraneliftId::Var(cl_var));
                        let cl_val =
                            self.expr_to_cl(fid, expr, fn_builder, obj_module, call_conv)?;
                        fn_builder.def_var(cl_var, cl_val);
                    }
                    _ => todo!(),
                };
            }
        };
        Ok(())
    }
    fn expr_to_cl(
        &mut self,
        callee_func_id: FuncId,
        expr: &AstExpr,
        fn_builder: &mut FunctionBuilder,
        obj_module: &mut ObjectModule,
        call_conv: CallConv,
    ) -> color_eyre::Result<Value> {
        let val = match &expr.kind {
            ExprKind::Atom(atom) => match atom {
                Atom::Ident((_, symbol_id)) => {
                    let symb = self.symbols.resolve_mut(symbol_id.unwrap());
                    match symb.cranelift_id.unwrap() {
                        CraneliftId::Var(variable) => fn_builder.use_var(variable),
                        CraneliftId::FnParam { block, param_index } => {
                            fn_builder.block_params(block)[param_index]
                        }
                        t => {
                            dbg!(t);
                            panic!();
                        }
                    }
                }
                Atom::Int(int_val) => fn_builder.ins().iconst(types::I32, *int_val as i64),
                Atom::Bool(val) => fn_builder.ins().iconst(types::I8, *val as i64),
                Atom::CStr(str_val) => {
                    let c_str_val = match &self.ast.tokens[*str_val].kind {
                        TokenKind::CStr(val) => val,
                        _ => unreachable!("CStr val wasn't mapped to a cstr token"),
                    };
                    let str_msg_id = obj_module.declare_data(
                        &format!("c_str_{}_{}-{}", "mod-name", expr.span.start, expr.span.end),
                        Linkage::Local,
                        false,
                        false,
                    )?;
                    let mut str_desc = DataDescription::new();
                    let mut c_val = c_str_val.clone();
                    c_val.push('\0');
                    str_desc.define(c_val.into_bytes().into_boxed_slice());
                    obj_module.define_data(str_msg_id, &str_desc)?;
                    let str_val_global =
                        obj_module.declare_data_in_func(str_msg_id, fn_builder.func);
                    let str_ptr = fn_builder.ins().global_value(types::I64, str_val_global);
                    str_ptr
                }
                Atom::Str(token_id) => {
                    // TODO: this needs to be replaced with the length aware struct version,
                    // Currently this is just a duplication of c string

                    let str_val = match &self.ast.tokens[*token_id].kind {
                        TokenKind::Str(val) => val,
                        _ => unreachable!("Str val wasn't mapped to a str token"),
                    };
                    let str_msg_id =
                        obj_module.declare_data("str_msg", Linkage::Local, false, false)?;
                    let mut str_desc = DataDescription::new();
                    str_desc.define(str_val.clone().into_bytes().into_boxed_slice());
                    obj_module.define_data(str_msg_id, &str_desc)?;
                    let str_val_global =
                        obj_module.declare_data_in_func(str_msg_id, fn_builder.func);
                    let str_ptr = fn_builder.ins().global_value(types::I64, str_val_global);
                    str_ptr
                }
            },
            ExprKind::Op(op) => match &**op {
                Op::FnCall {
                    ident: ident_expr,
                    args,
                } => {
                    let ident_symb = match &ident_expr.kind {
                        ExprKind::Atom(Atom::Ident((_, symb_id))) => {
                            self.symbols.resolve(symb_id.unwrap())
                        }
                        t => panic!("tried calling a funtion with an ident that was {:?}", t),
                    };
                    let cl_func_id = match ident_symb.cranelift_id {
                        Some(CraneliftId::Func(v)) => v,
                        t => unreachable!(
                            "got a none cranelift function id for function symbol: {t:?}"
                        ),
                    };

                    let fn_in_fn = FnInFn {
                        from: callee_func_id,
                        calling: cl_func_id,
                    };
                    let local_fn = match self.func_defs_in_funcs.get(&fn_in_fn) {
                        Some(v) => *v,
                        None => {
                            let local_fn =
                                obj_module.declare_func_in_func(cl_func_id, fn_builder.func);
                            self.func_defs_in_funcs.insert(fn_in_fn, local_fn);
                            local_fn
                        }
                    };

                    let cl_fn_args = {
                        let mut cl_args = vec![];
                        for arg in args {
                            cl_args.push(self.expr_to_cl(
                                callee_func_id,
                                arg,
                                fn_builder,
                                obj_module,
                                call_conv,
                            )?);
                        }
                        cl_args
                    };
                    let call_inst = fn_builder.ins().call(local_fn, &cl_fn_args);

                    let res = fn_builder.inst_results(call_inst);
                    // TODO: probably need to replace all to return a slice
                    res[0]
                }
                Op::Add { left, right } => {
                    let left_val =
                        self.expr_to_cl(callee_func_id, left, fn_builder, obj_module, call_conv)?;
                    let right_val =
                        self.expr_to_cl(callee_func_id, right, fn_builder, obj_module, call_conv)?;
                    fn_builder.ins().iadd(left_val, right_val)
                }
                Op::Minus { left, right } => {
                    let left_val =
                        self.expr_to_cl(callee_func_id, left, fn_builder, obj_module, call_conv)?;
                    let right_val =
                        self.expr_to_cl(callee_func_id, right, fn_builder, obj_module, call_conv)?;
                    fn_builder.ins().isub(left_val, right_val)
                }
                Op::Multiply { left, right } => {
                    let left_val =
                        self.expr_to_cl(callee_func_id, left, fn_builder, obj_module, call_conv)?;
                    let right_val =
                        self.expr_to_cl(callee_func_id, right, fn_builder, obj_module, call_conv)?;
                    fn_builder.ins().imul(left_val, right_val)
                }
                Op::Ref(ref_expr) => {
                    // TOOD: this is definietly wrong but it might work for now
                    let ref_cl_val = self.expr_to_cl(
                        callee_func_id,
                        ref_expr,
                        fn_builder,
                        obj_module,
                        call_conv,
                    )?;
                    ref_cl_val
                }
                Op::IfCond {
                    condition,
                    block,
                    else_ifs,
                    unconditional_else,
                } => {
                    if expr.type_id.is_some() {
                        todo!("implement if statements returning values in cranelift")
                    }
                    if else_ifs.len() > 1 {
                        todo!("implement else if branches in cranelift")
                    }
                    let c = self.expr_to_cl(
                        callee_func_id,
                        condition,
                        fn_builder,
                        obj_module,
                        call_conv,
                    )?;

                    let then_block = fn_builder.create_block();
                    let else_block = fn_builder.create_block();
                    let merge_block = fn_builder.create_block();

                    fn_builder.ins().brif(c, then_block, [], else_block, []);

                    fn_builder.switch_to_block(then_block);
                    fn_builder.seal_block(then_block);
                    let mut then_return = fn_builder.ins().iconst(types::I32, 0);
                    for statement in &block.statements {
                        self.statement_to_cl(
                            callee_func_id,
                            statement,
                            fn_builder,
                            obj_module,
                            call_conv,
                        )?;
                    }

                    // Jump to the merge block, passing it the block return value.
                    fn_builder.ins().jump(merge_block, []);

                    fn_builder.switch_to_block(else_block);
                    fn_builder.seal_block(else_block);
                    let mut else_return = fn_builder.ins().iconst(types::I32, 0);
                    for statement in &unconditional_else.as_ref().unwrap().statements {
                        self.statement_to_cl(
                            callee_func_id,
                            statement,
                            fn_builder,
                            obj_module,
                            call_conv,
                        )?;
                    }

                    // Jump to the merge block, passing it the block return value.
                    fn_builder.ins().jump(merge_block, &[]);

                    // Switch to the merge block for subsequent statements.
                    fn_builder.switch_to_block(merge_block);

                    // We've now seen all the predecessors of the merge block.
                    fn_builder.seal_block(merge_block);
                    else_return
                }
                t => {
                    dbg!(t);
                    todo!();
                }
            },
        };

        Ok(val)
    }
}

trait ToClType {
    fn to_cl_type(&self) -> types::Type;
}
impl ToClType for TypeKind {
    fn to_cl_type(&self) -> types::Type {
        match self {
            TypeKind::Int => types::I32,
            TypeKind::Uint => types::I32,
            TypeKind::Bool => types::I8,
            TypeKind::Str => todo!(),
            TypeKind::CStr => todo!(),
            TypeKind::Void => todo!(),
            TypeKind::Struct {
                struct_id: _,
                fields: _,
            } => todo!(),
            TypeKind::Fn { .. } => todo!(),
            TypeKind::Ref(_) => types::I64,
            TypeKind::Unknown => todo!(),
            TypeKind::Var => todo!(),
        }
    }
}
