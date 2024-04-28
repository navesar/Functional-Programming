// L5-typecheck
// ========================================================
import { concat, equals, map, zipWith } from 'ramda';
import { isAppExp, isBoolExp, isDefineExp, isIfExp, isLetrecExp, isLetExp, isNumExp,
         isPrimOp, isProcExp, isProgram, isStrExp, isVarRef, parseL5Exp, unparse,
         AppExp, BoolExp, DefineExp, Exp, IfExp, LetrecExp, LetExp, NumExp,
         Parsed, PrimOp, ProcExp, Program, StrExp, isBinding, makeProgram } from "./L5-ast";
import { applyTEnv, makeEmptyTEnv, makeExtendTEnv, TEnv } from "./TEnv";
import { isProcTExp, makeBoolTExp, makeNumTExp, makeProcTExp, makeStrTExp, makeVoidTExp,
          unparseTExp,
         BoolTExp, NumTExp, StrTExp, TExp, VoidTExp, makeUnionTExp, UnionTExp, isAtomicTExp, isUnionTExp, ProcTExp } from "./TExp";
import { isEmpty, allT, first, rest, NonEmptyList, List, isNonEmptyList } from '../shared/list';
import { Result, makeFailure, bind, makeOk, zipWithResult, isFailure } from '../shared/result';
import { parse as p } from "../shared/parser";
import { format } from '../shared/format';
import { parseTE } from './TExp';
import { json } from 'stream/consumers';

// TODO L51
// Purpose: Check that type expressions are compatible
// as part of a fully-annotated type check process of exp.
// Return an error if te1 is not compatible with te2 - true otherwise.
// Exp is only passed for documentation purposes.
export const checkCompatibleType = (te1: TExp, te2: TExp, exp: Exp): Result<true> =>{
    if(equals(te1, te2) || (isUnionTExp(te1) && !isUnionTExp(te2) && te1.comps.length === 1 && equals(te1.comps[0], te2)))
        return makeOk(true);
    if(isProcTExp(te1) && isProcTExp(te2))
        return compProcsTypes(te1, te2, exp) ? makeOk(true) : fail(te1, te2, exp);
    if(isProcTExp(te1) || isProcTExp(te2))
        fail(te1, te2, exp);
    if(!isUnionTExp(te1) && !isUnionTExp(te2))
        return  equals(te1, te2) ? makeOk(true) : fail(te1, te2, exp);
    if(!isUnionTExp(te1) && isUnionTExp(te2))
        return  te2.comps.map((te: TExp) => te.tag).includes(te1.tag) ? makeOk(true) : fail(te1, te2, exp);
    if(isUnionTExp(te1) && isUnionTExp(te2))
        return  includedIn(te1.comps, te2.comps, 0) ? makeOk(true) : fail(te1, te2, exp);
    return  fail(te1, te2, exp);
}
const fail = (te1: TExp, te2: TExp, exp: Exp): Result<true> =>
    bind(unparseTExp(te1), (te1: string) =>
        bind(unparseTExp(te2), (te2: string) =>
            bind(unparse(exp), (exp: string) => 
                makeFailure<true>(`Incompatible types: ${te1} and ${te2} in ${exp}`))));

const includedIn = (small: TExp[], big: TExp[], index: number): boolean =>
    big.length < small.length ? false :
    index >= small.length ? true :
    big.map((te: TExp) => te.tag).includes(small[index].tag) ? includedIn(small, big, index+1) :
    false;

const compProcsTypes = (te1: ProcTExp, te2: ProcTExp, exp: Exp): boolean =>
    te1.paramTEs.length === te2.paramTEs.length && !isFailure(checkCompatibleType(te1.returnTE, te2.returnTE, exp)) && includedIn2(te2.paramTEs, te1.paramTEs);

const includedIn2 = (jeden: TExp[], dva: TExp[]): boolean =>{
    if(jeden.length !== dva.length)
        return false;
    if(jeden.length === 0) 
        return true;
    if(isUnionTExp(dva[0])){
        if(isUnionTExp(jeden[0])){
            if(includedIn(jeden[0].comps, dva[0].comps, 0))
                return includedIn2(jeden.slice(1), dva.slice(1));
            else
                return false;
        }
        else if(dva[0].comps.map((te: TExp) => te.tag).includes(jeden[0].tag))
            return includedIn2(jeden.slice(1), dva.slice(1));
        else
            return false; 
    }
    if(isUnionTExp(jeden[0])){
        if(jeden[0].comps.length === 1){
            if(equals(jeden[0].comps[0], dva[0]))
                return includedIn2(jeden.slice(1), dva.slice(1));
            else
                return false;
        }
        else
            return false;
    }
    if(equals(dva[0], jeden[0]))
        return includedIn2(jeden.slice(1), dva.slice(1));
    return false;
}



// Compute the type of L5 AST exps to TE
// ===============================================
// Compute a Typed-L5 AST exp to a Texp on the basis
// of its structure and the annotations it contains.

// Purpose: Compute the type of a concrete fully-typed expression
export const L5typeof = (concreteExp: string): Result<string> =>
    bind(p(concreteExp), (x) =>
        bind(parseL5Exp(x), (e: Exp) => 
            bind(typeofExp(e, makeEmptyTEnv()), unparseTExp)));

// Purpose: Compute the type of an expression
// Traverse the AST and check the type according to the exp type.
// We assume that all variables and procedures have been explicitly typed in the program.
export const typeofExp = (exp: Parsed, tenv: TEnv): Result<TExp> =>
    isNumExp(exp) ? makeOk(typeofNum(exp)) :
    isBoolExp(exp) ? makeOk(typeofBool(exp)) :
    isStrExp(exp) ? makeOk(typeofStr(exp)) :
    isPrimOp(exp) ? typeofPrim(exp) :
    isVarRef(exp) ? applyTEnv(tenv, exp.var) :
    isIfExp(exp) ? typeofIf(exp, tenv) :
    isProcExp(exp) ? typeofProc(exp, tenv) :
    isAppExp(exp) ? typeofApp(exp, tenv) :
    isLetExp(exp) ? typeofLet(exp, tenv) :
    isLetrecExp(exp) ? typeofLetrec(exp, tenv) :
    isDefineExp(exp) ? typeofDefine(exp, tenv) :
    isProgram(exp) ? typeofProgram(exp, tenv) :
    makeFailure(`Unknown type: ${format(exp)}`);

// Purpose: Compute the type of a sequence of expressions
// Check all the exps in a sequence - return type of last.
// Pre-conditions: exps is not empty.
export const typeofExps = (exps: List<Exp>, tenv: TEnv): Result<TExp> =>
    isNonEmptyList<Exp>(exps) ? 
        isEmpty(rest(exps)) ? typeofExp(first(exps), tenv) :
        bind(typeofExp(first(exps), tenv), _ => typeofExps(rest(exps), tenv)) :
    makeFailure(`Unexpected empty list of expressions`);


// a number literal has type num-te
export const typeofNum = (n: NumExp): NumTExp => makeNumTExp();

// a boolean literal has type bool-te
export const typeofBool = (b: BoolExp): BoolTExp => makeBoolTExp();

// a string literal has type str-te
const typeofStr = (s: StrExp): StrTExp => makeStrTExp();

// primitive ops have known proc-te types
const numOpTExp = parseTE('(number * number -> number)');
const numCompTExp = parseTE('(number * number -> boolean)');
const boolOpTExp = parseTE('(boolean * boolean -> boolean)');

// Todo: cons, car, cdr, list
export const typeofPrim = (p: PrimOp): Result<TExp> =>
    (p.op === '+') ? numOpTExp :
    (p.op === '-') ? numOpTExp :
    (p.op === '*') ? numOpTExp :
    (p.op === '/') ? numOpTExp :
    (p.op === 'and') ? boolOpTExp :
    (p.op === 'or') ? boolOpTExp :
    (p.op === '>') ? numCompTExp :
    (p.op === '<') ? numCompTExp :
    (p.op === '=') ? numCompTExp :
    // Important to use a different signature for each op with a TVar to avoid capture
    (p.op === 'number?') ? parseTE('(T -> boolean)') :
    (p.op === 'boolean?') ? parseTE('(T -> boolean)') :
    (p.op === 'string?') ? parseTE('(T -> boolean)') :
    (p.op === 'list?') ? parseTE('(T -> boolean)') :
    (p.op === 'pair?') ? parseTE('(T -> boolean)') :
    (p.op === 'symbol?') ? parseTE('(T -> boolean)') :
    (p.op === 'not') ? parseTE('(boolean -> boolean)') :
    (p.op === 'eq?') ? parseTE('(T1 * T2 -> boolean)') :
    (p.op === 'string=?') ? parseTE('(T1 * T2 -> boolean)') :
    (p.op === 'display') ? parseTE('(T -> void)') :
    (p.op === 'newline') ? parseTE('(Empty -> void)') :
    makeFailure(`Primitive not yet implemented: ${p.op}`);

// TODO L51
export const makeUnion = (te1: TExp, te2: TExp): UnionTExp =>
    makeUnionTExp(te1, te2);





// TODO L51
// Purpose: compute the type of an if-exp
// Typing rule:
//   if type<test>(tenv) = boolean
//      type<then>(tenv) = t1
//      type<else>(tenv) = t1
// then type<(if test then else)>(tenv) = t1
export const typeofIf = (ifExp: IfExp, tenv: TEnv): Result<TExp> => {
    const testTE = typeofExp(ifExp.test, tenv);
    const thenTE = typeofExp(ifExp.then, tenv);
    const altTE = typeofExp(ifExp.alt, tenv);
    const constraint1 = bind(testTE, testTE => checkCompatibleType(testTE, makeBoolTExp(), ifExp));
    return bind(constraint1, (_c1: true) =>
        bind(thenTE, (thente) => bind(altTE, (altte) => makeOk(makeUnionTExp(thente, altte)))));
};

// Purpose: compute the type of a proc-exp
// Typing rule:
// If   type<body>(extend-tenv(x1=t1,...,xn=tn; tenv)) = t
// then type<lambda (x1:t1,...,xn:tn) : t exp)>(tenv) = (t1 * ... * tn -> t)
export const typeofProc = (proc: ProcExp, tenv: TEnv): Result<TExp> => {
    const argsTEs = map((vd) => vd.texp, proc.args);
    const extTEnv = makeExtendTEnv(map((vd) => vd.var, proc.args), argsTEs, tenv);
    const constraint1 = bind(typeofExps(proc.body, extTEnv), (body: TExp) => 
                            checkCompatibleType(body, proc.returnTE, proc));
    return bind(constraint1, _ => makeOk(makeProcTExp(argsTEs, proc.returnTE)));
};

// Purpose: compute the type of an app-exp
// Typing rule:
// If   type<rator>(tenv) = (t1*..*tn -> t)
//      type<rand1>(tenv) = t1
//      ...
//      type<randn>(tenv) = tn
// then type<(rator rand1...randn)>(tenv) = t
// We also check the correct number of arguments is passed.
export const typeofApp = (app: AppExp, tenv: TEnv): Result<TExp> =>
    bind(typeofExp(app.rator, tenv), (ratorTE: TExp) => {
        if (! isProcTExp(ratorTE)) {
            return bind(unparseTExp(ratorTE), (rator: string) =>
                        bind(unparse(app), (exp: string) =>
                            makeFailure<TExp>(`Application of non-procedure: ${rator} in ${exp}`)));
        }
        if (app.rands.length !== ratorTE.paramTEs.length) {
            return bind(unparse(app), (exp: string) => makeFailure<TExp>(`Wrong parameter numbers passed to proc: ${exp}`));
        }
        const constraints = zipWithResult((rand, trand) => bind(typeofExp(rand, tenv), (typeOfRand: TExp) => 
                                                                checkCompatibleType(typeOfRand, trand, app)),
                                          app.rands, ratorTE.paramTEs);
        return bind(constraints, _ => makeOk(ratorTE.returnTE));
    });

// Purpose: compute the type of a let-exp
// Typing rule:
// If   type<val1>(tenv) = t1
//      ...
//      type<valn>(tenv) = tn
//      type<body>(extend-tenv(var1=t1,..,varn=tn; tenv)) = t
// then type<let ((var1 val1) .. (varn valn)) body>(tenv) = t
export const typeofLet = (exp: LetExp, tenv: TEnv): Result<TExp> => {
    const vars = map((b) => b.var.var, exp.bindings);
    const vals = map((b) => b.val, exp.bindings);
    const varTEs = map((b) => b.var.texp, exp.bindings);
    const constraints = zipWithResult((varTE, val) => bind(typeofExp(val, tenv), (typeOfVal: TExp) => 
                                                            checkCompatibleType(varTE, typeOfVal, exp)),
                                      varTEs, vals);
    return bind(constraints, _ => typeofExps(exp.body, makeExtendTEnv(vars, varTEs, tenv)));
};

// Purpose: compute the type of a letrec-exp
// We make the same assumption as in L4 that letrec only binds proc values.
// Typing rule:
//   (letrec((p1 (lambda (x11 ... x1n1) body1)) ...) body)
//   tenv-body = extend-tenv(p1=(t11*..*t1n1->t1)....; tenv)
//   tenvi = extend-tenv(xi1=ti1,..,xini=tini; tenv-body)
// If   type<body1>(tenv1) = t1
//      ...
//      type<bodyn>(tenvn) = tn
//      type<body>(tenv-body) = t
// then type<(letrec((p1 (lambda (x11 ... x1n1) body1)) ...) body)>(tenv-body) = t
export const typeofLetrec = (exp: LetrecExp, tenv: TEnv): Result<TExp> => {
    const ps = map((b) => b.var.var, exp.bindings);
    const procs = map((b) => b.val, exp.bindings);
    if (! allT(isProcExp, procs))
        return makeFailure(`letrec - only support binding of procedures - ${format(exp)}`);
    const paramss = map((p) => p.args, procs);
    const bodies = map((p) => p.body, procs);
    const tijs = map((params) => map((p) => p.texp, params), paramss);
    const tis = map((proc) => proc.returnTE, procs);
    const tenvBody = makeExtendTEnv(ps, zipWith((tij, ti) => makeProcTExp(tij, ti), tijs, tis), tenv);
    const tenvIs = zipWith((params, tij) => makeExtendTEnv(map((p) => p.var, params), tij, tenvBody),
                           paramss, tijs);
    const types = zipWithResult((bodyI, tenvI) => typeofExps(bodyI, tenvI), bodies, tenvIs)
    const constraints = bind(types, (types: TExp[]) => 
                            zipWithResult((typeI, ti) => checkCompatibleType(typeI, ti, exp), types, tis));
    return bind(constraints, _ => typeofExps(exp.body, tenvBody));
};

// Typecheck a full program
// TODO L51
// TODO: Thread the TEnv (as in L1)

// Purpose: compute the type of a define
// Typing rule:
//   (define (var : texp) val)
// TODO L51 - write the true definition
// if type<val> = T1
// then type((define (var : texp) val)) (extend-tenv(var = T1, tenv)) = void
export const typeofDefine = (exp: DefineExp, tenv: TEnv): Result<VoidTExp> =>{
    const varTE = exp.var.texp;
    const valTE = typeofExp(exp.val, tenv);
    const constraint = bind(valTE, valTE => checkCompatibleType(varTE, valTE, exp))
    return bind(constraint, (t: true) => makeOk(makeVoidTExp()));
}
    

// Purpose: compute the type of a program
// Typing rule:
// if type(en.var) = Tn (last var) and if e1 = void,..., en.var = Tn 
// then type<program>(tenv) = Tn
// TODO - write the true definition
export const typeofProgram = (exp: Program, tenv: TEnv): Result<TExp> =>{
    const exps: Exp[] = exp.exps;
    if(exps.length === 0)
        return makeFailure('Program is an empty list of exps');
    if(exps.length === 1)
        return typeofExp(exps[0], tenv);
    if(isDefineExp(exps[0])){
        const def = exps[0] as DefineExp;
        const updatedTenv = bind(typeofExp(def.val, tenv), (te: TExp) => makeOk(makeExtendTEnv([def.var.var], [te], tenv)));
        return bind(updatedTenv, (tenv2: TEnv) => typeofProgram(makeProgram(exps.slice(1)), tenv2));
    }
    else
        return typeofProgram(makeProgram(exps.slice(1)), tenv);
}


