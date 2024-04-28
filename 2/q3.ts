import {  AppExp, CExp, CondExp, DefineExp, Exp, IfExp, LetExp, ProcExp, Program, isAppExp, isCompoundExp, isCondExp, isDefineExp, isExp, isIfExp, isLetExp, isProcExp, isProgram, makeAppExp, makeDefineExp, makeIfExp, makeLetExp, makeProcExp, makeProgram, makeStrExp } from "./L31-ast";
import { Result, makeFailure, makeOk, isOk } from "../shared/result";
import exp from "constants";
import { map } from "ramda";
import { error } from "console";


/*
Purpose: Transform L31 AST to L3 AST
Signature: l31ToL3(l31AST)
Type: [Exp | Program] => Result<Exp | Program>
*/
export const L31ToL3 = (exp: Exp | Program): Result<Exp | Program> =>
    !(isExp(exp) || isProgram(exp)) ? makeFailure("invalid L31 arg") :
    isExp(exp) ? ExpToL3(exp) :
    programToL3(exp).exps.includes(makeStrExp("error")) ? makeFailure("error") :
    makeOk(programToL3(exp));



export const programToL3 = (prog: Program) : Program =>
    makeProgram(map((res: Result<Exp>) => isOk(res) ? res.value : makeStrExp(res.message) , prog.exps.map(ExpToL3)))


export const ExpToL3 = (exp: Exp) : Result<Exp> =>
    !isExp(exp) ? makeFailure("error") :
    isAppExp(exp) ? AppToL3(exp) :
    isIfExp(exp) ? IfExpToL3 (exp) :
    isProcExp(exp) ? procExpTolL3(exp) :
    isLetExp(exp) ? letToL3(exp) :
    isDefineExp(exp) ? defineToL3(exp) :
    !isCondExp(exp) ? makeOk(exp) :
    makeOk(CondExpToL3(exp,0));

export const arrayTolL3 = (arr : Exp[]) : Result<CExp[]> =>{
    const checkMe = (map((res: Result<Exp>) => isOk(res) ? res.value : makeStrExp(res.message) , arr.map(ExpToL3)));
    if(checkMe.includes(makeStrExp("error")))  
        return makeFailure("error");
    else 
        return makeOk(checkMe as CExp[]);
}

export const CondExpToL3 = (cond: CondExp, index: number) : IfExp =>
    index === cond.condClauses.length-2 ? makeIfExp(cond.condClauses[index].test, cond.condClauses[index].then[0],  cond.condClauses[index + 1].then[0]) :
    makeIfExp(cond.condClauses[index].test, cond.condClauses[index].then[0], CondExpToL3(cond, index+1))


export const AppToL3 = (Appex: AppExp) : Result<Exp> =>{
    const app2L3 = arrayTolL3(Appex.rands);
    if(isOk(app2L3)) 
        return makeOk(makeAppExp(Appex.rator ,app2L3.value as CExp[]));
    else
        return makeFailure("error");
}
    

export const IfExpToL3 = (ifex: IfExp) : Result<Exp> =>{
    const testL3 = ExpToL3(ifex.test);
    const thenL3 = ExpToL3(ifex.then);
    const elseL3 = ExpToL3(ifex.alt);
    if(isOk(testL3) && isOk(thenL3) && isOk(elseL3))
        return makeOk(makeIfExp(testL3.value as CExp, thenL3.value as CExp, elseL3.value as CExp));
    else
        return makeFailure("error");
}
    

export const procExpTolL3 = (proc: ProcExp) : any =>{
    const proc2L3 = arrayTolL3(proc.body);
    if(isOk(proc2L3))
        return makeOk(makeProcExp(proc.args ,proc2L3.value as CExp[]));
    else
        return makeFailure("error");
}


export const letToL3 = (letex: LetExp) : any =>{
    const let2L3 = arrayTolL3(letex.body);
    if (isOk(let2L3))
    return  makeOk(makeLetExp(letex.bindings ,let2L3.value as CExp[]));
    else
        return makeFailure("error");
}    


export const defineToL3 = (def: DefineExp) : any =>{
    const define2L3 = ExpToL3(def.val);
    if (isOk(define2L3))
        return makeOk(makeDefineExp(def.var ,define2L3.value as CExp));
    else
        return makeFailure("error");
}
    
