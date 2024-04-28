import exp from 'constants';
import { Exp, Program, CExp, DefineExp, VarDecl, Binding } from '../imp/L3-ast';
import { isAtomicExp, isBoolExp, isLetExp, isPrimOp, isStrExp } from '../imp/L3-ast';
import { Result, makeFailure, makeOk } from '../shared/result';
import { isAppExp, isDefineExp, isExp, isIfExp, isNumExp, isProcExp, isProgram } from './L31-ast';

/*
Purpose: Transform L2 AST to Python program string
Signature: l2ToPython(l2AST)
Type: [Parsed | Error] => Result<string>
*/
export const l2ToPython = (exp: Exp | Program): Result<string>  => {
    if(isProgram(exp)){
        const progToPy = progToPython(exp.exps, 0);
        if(!progToPy.includes("errorFlag!")) 
            return makeOk(progToPy);
        else
            return makeFailure("error");
    }
    else{
        if(isExp(exp)){ //exp is Exp
            const ExpToPy = ExpToPython(exp);
            if(!ExpToPy.includes("errorFlag!"))         
                return makeOk(ExpToPy);
            else
                return makeFailure("error");
        }
        else
            return makeFailure("illegal input");
    }
}


export const progToPython = (exp: Exp[], index: number): string => 
    index >= exp.length? "":
    index === exp.length-1 ? ExpToPython(exp[index]) + progToPython(exp, index+1):
    ExpToPython(exp[index]) +"\n"+ progToPython(exp, index+1);

export const ExpToPython = (exp: Exp) :string =>
    isDefineExp(exp) ? DefineExpToPython(exp) : CExpToPython(exp);

export const CExpToPython = (exp:CExp) : string =>{
    if(isAtomicExp(exp)){
        if(isNumExp(exp) || isStrExp(exp))
            return exp.val.toString();
        else if(isBoolExp(exp)){
            if(exp.val)
                return "True";
            return "False";
        }
        else{ //primOp or VarEf
            if(isPrimOp(exp)){
                if(exp.op !== "=")
                    return exp.op;
                return "==";
            }
            
            else // VarEf
                return exp.var;
        } 
    }
    else{ //compundExp
        if(isAppExp(exp)){
            const operator: string = CExpToPython(exp.rator);
            if(exp.rands.length === 1){
                if(operator === "number?")
                    return "isinstance("+CExpToPython(exp.rands[0])+", (int, float, complex))";
                else if(operator === "boolean?")
                    return "isinstance("+CExpToPython(exp.rands[0])+", bool)";
                else if(operator === "not")
                    return "(not " + CExpToPython(exp.rands[0])+")";
                else 
                    return functionOperator(operator, exp.rands, 0);
            }
            else{
                if(exp.rands.length > 0){
                    if(operator === "eq?"){
                        if(exp.rands.length === 2)
                            return CExpToPython(exp.rands[0]) +" == "+ CExpToPython(exp.rands[1]);
                        else
                            return "eq? with "+exp.rands.length+" rands";
                        }
                    else if(isPrimOpStr(operator))
                        return multipleRandsOneRator(operator, exp.rands, 0);
                    
                    else
                        return functionOperator(operator, exp.rands, 0);
                }
                else
                    return "errorFlag! 0 rands in ExpToPython() (compundExo)";
            }
        }
        else if(isIfExp(exp))
            return "("+CExpToPython(exp.then) +" if "+ CExpToPython(exp.test)+ " else " +CExpToPython(exp.alt)+")";
        else if(isProcExp(exp))
            return "(lambda "+varDecToPy(exp.args,0)+" : "+CExpArrayToPy(exp.body,0)+")";
        else if(isLetExp(exp))
            return bindingsToPy(exp.bindings, 0) + CExpArrayToPy(exp.body,0);
        else
            return "errorFlag! error in ExpToPython";
    } 
}

export const DefineExpToPython = (exp: DefineExp) : string =>
    exp.var.var + " = " +CExpToPython(exp.val);

export const varDecToPy = (varDec: VarDecl[], index: number) : string =>
    (index >= varDec.length) ? "":
    index === 0 ? varDec[index].var + varDecToPy(varDec, index+1) :
    ","+varDec[index].var + varDecToPy(varDec, index+1);

export const CExpArrayToPy = (cexpArray: CExp[], index: number): string =>{
    if(index > cexpArray.length || index === cexpArray.length)
        return "";
    return CExpToPython(cexpArray[index]) + CExpArrayToPy(cexpArray, index+1);
}

export const isPrimOpStr = (op: string) : boolean =>
     op === "+" || op === "-" || op === "*"|| op === "/" ||op === ">" || op === "<" || op === "=" || op === "==";

export const bindingsToPy = (bindings: Binding[], index: number): string =>
    index >= bindings.length ? "" :
    bindings[index].var.var +" = "+CExpToPython(bindings[index].val)+bindingsToPy(bindings, index+1);

export const multipleRandsOneRator = (operator: string, rands: CExp[], index: number) : string =>
    index >= rands.length ? ")" :
    index === 0 ? "(" + CExpToPython(rands[0]) + multipleRandsOneRator(operator, rands, index + 1) :
    " "+ operator+" " + CExpToPython(rands[index]) + multipleRandsOneRator(operator, rands, index + 1);

export const functionOperator = (operator: string, rands: CExp[], index: number): string =>
    index >= rands.length ? ")" :
    index === 0 ? operator+"("+CExpToPython(rands[index])+functionOperator(operator,rands,index+1) :
    ","+CExpToPython(rands[index]) +functionOperator(operator,rands,index+1);

