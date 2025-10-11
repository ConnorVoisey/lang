# Lang

Basic compiler with minimal functionality.

## Roadmap

### Phase 0: Basics
- [x] **Lexer** - Tokenization with span tracking for error reporting
- [x] **AST parser** - Recursive descent parser with error recovery
- [x] **Symbol table** - Scoped symbol resolution with stack of hash maps
- [x] **Type system** - Union-find based type inference and unification
- [x] **Type checker** - Validates types and control flow
- [x] **Functions** - Typed parameters and return values
- [x] **Extern "C" declarations** - FFI for calling C functions (e.g., printf)
- [x] **Function calls** - With argument passing
- [x] **Variables** - `let` declarations (immutable)
- [x] **Assignments** - Updating variable values
- [x] **If/else conditionals** - With block expressions
- [x] **While loops** - Basic iteration
- [x] **Break statements** - Early loop exit
- [x] **Block expressions** - Implicit returns from blocks
- [x] **Arithmetic operators** - `+`, `-`, `*`, `/`
- [x] **Comparison operators** - `<`, `<=`, `>`, `>=`, `==`
- [x] **Primitive types** - Int, Uint, Bool
- [x] **C-string literals** - `&c"..."` for C interop
- [x] **References** - `&` operator (basic implementation)
- [x] **Cranelift backend** - Code generation to object files
- [x] **Linking** - Via TCC to produce executables
- [x] **Error reporting** - With codespan-reporting for nice diagnostics
- [x] **String interning** - Efficient identifier storage
- [x] **Struct definitions** - Named fields with types
- [~] **Struct field access** - Dot notation (`foo.num`)
- [~] **Struct instantiation** - Creating struct instances with field initialization

### Phase 1: Core Infrastructure
- [ ] **Basic structs** - Field access, instantiation (in progress)
- [ ] **Actually use HLIR SSA** - Switch from AST→Cranelift to AST→HLIR→Cranelift to avoid reimplementing features
- [ ] **Arrays and slices** - Fixed-size arrays `[T; N]`, dynamic slices `[T]`
- [ ] **String type implementation** - Proper length-aware strings (currently TODO in codegen)
- [ ] **For loops** - Syntactic sugar over while/iterators

### Phase 2: Memory Management
- [ ] **Basic garbage collector** - Integrate bdwgc
- [ ] **Struct escape analysis** - Optimize by stack-allocating non-escaping values
- [ ] **Mutability system** - Opt-in `mut` keyword for variables and struct fields

### Phase 3: Type System Extensions
- [ ] **Basic enums** - C-style enums without associated data
- [ ] **Generics/parametric polymorphism** - `fn foo<T>(x: T)`, `struct Vec<T>`
- [ ] **Option type** - `Option<T>` for null safety, with Some/None variants
- [ ] **Tagged unions (proper enums)** - Rust-style enums with associated data
- [ ] **Nested tagged unions** - Enums containing other enums

### Phase 4: Pattern Matching
- [ ] **Match keyword (non-exhaustive)** - Basic pattern matching with wildcard fallback
- [ ] **Match keyword (exhaustive)** - Compiler-enforced exhaustiveness checking
- [ ] **Match on tagged unions** - Extract associated data from enum variants
- [ ] **Advanced patterns** - Nested patterns, guards, multiple patterns per arm

### Phase 5: Error Handling & Traits
- [ ] **Result type** - `Result<T, E>` for error handling
- [ ] **Question mark operator** - `?` for error propagation
- [ ] **Traits/interfaces** - Basic trait definitions and implementations
- [ ] **Struct methods** - `foo.bar()` syntax, self parameter
- [ ] **Trait bounds** - Generic constraints `fn foo<T: Display>(x: T)`
- [ ] **Core traits** - Debug, Display, Clone, Copy, Default, Iterator

### Phase 6: Modules & Organization
- [ ] **Module system** - Proper file-based modules, visibility rules
- [ ] **Package system** - Dependencies, versioning, build system
- [ ] **Module-level organization** - Public/private exports

### Phase 7: Standard Library Foundation
- [ ] **Start standard library** - Core types (Vec, HashMap, String utilities)
- [ ] **I/O primitives** - File, stdout/stderr, buffering
- [ ] **Collections** - Vec, HashMap, HashSet
- [ ] **Iterator trait and adapters** - map, filter, fold, etc.

### Phase 8: Compile-Time Introspection
- [ ] **Query struct fields** - Access field names, types at compile time
- [ ] **Struct annotations** - Go-style tags/attributes on fields and types
- [ ] **Query struct annotations** - Read metadata at compile time
- [ ] **Type information as constants** - Expose type metadata as const values

### Phase 9: Optimization & Performance
- [ ] **Look into constant folding** - Determine what Cranelift does vs frontend needs
- [ ] **Basic HLIR optimizations** - DCE, constant propagation, simple inlining
- [ ] **Evaluate RVSDG** - Benchmark compile time vs runtime performance gains
- [ ] **Implement RVSDG (if beneficial)** - Possibly opt-in per function
- [ ] **Advanced escape analysis** - Leverage for more aggressive optimizations

### Phase 10: Production Readiness
- [ ] **Incremental compilation** - Module caching, dependency tracking
- [ ] **Parallel compilation** - Multi-threaded module compilation
- [ ] **Better diagnostics** - "Did you mean?", fix suggestions, better error messages
- [ ] **Documentation system** - Doc comments, doc generation
- [ ] **Testing framework** - Built-in test runner, assertions
- [ ] **Benchmarking support** - Built-in benchmark framework
- [ ] **Custom GC implementation** - Replace bdwgc with Cranelift stack map based GC

### Future Considerations
- Closures and lambdas
- Async/await, threads, fibers
- Defer statement for cleanup
- Bitwise operations
- More advanced memory control (arenas, custom allocators)
- SIMD support (auto vectorisation unlikely) 
- FFI improvements beyond extern "C"
- Inline assembly (hard with cranelift but might be a requirement)
- Reflection (if const introspection proves insufficient)
