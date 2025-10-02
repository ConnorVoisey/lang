use cranelift::prelude::Block;
use cranelift_frontend::Variable;
use cranelift_module::FuncId;

#[derive(Copy, Clone, Debug)]
pub enum CraneliftId {
    FnId(ClFnId),
    FnParamId(ClFnParamId),
    VarId(ClVarId),
}

#[derive(Clone, Copy, Debug, Hash, PartialEq)]
pub struct ClFnId(usize);

#[derive(Clone, Copy, Debug, Hash, PartialEq)]
pub struct ClFnParamId(usize);

#[derive(Clone, Copy, Debug, Hash, PartialEq)]
pub struct ClVarId(usize);

#[derive(Debug, Default)]
pub struct ClVals {
    fns: Vec<FuncId>,
    fn_params: Vec<(Block, usize)>,
    vars: Vec<Variable>,
}

impl ClVals {
    pub fn insert_fn(&mut self, func_id: FuncId) -> ClFnId {
        let id = self.fns.len();
        self.fns.push(func_id);
        ClFnId(id)
    }
    pub fn get_fn(&self, cl_fn_id: ClFnId) -> &FuncId {
        &self.fns[cl_fn_id.0]
    }

    pub fn insert_fn_param(&mut self, block: Block, param_index: usize) -> ClFnParamId {
        let id = self.fn_params.len();
        self.fn_params.push((block, param_index));
        ClFnParamId(id)
    }
    pub fn get_fn_param(&self, cl_fn_param_id: ClFnParamId) -> &(Block, usize) {
        &self.fn_params[cl_fn_param_id.0]
    }

    pub fn insert_var(&mut self, var: Variable) -> ClVarId {
        let id = self.vars.len();
        self.vars.push(var);
        ClVarId(id)
    }
    pub fn get_var(&self, cl_var_id: ClVarId) -> &Variable {
        &self.vars[cl_var_id.0]
    }
}
