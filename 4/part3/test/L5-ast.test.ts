import { isNumExp, isBoolExp, isVarRef, isPrimOp, isProgram, isDefineExp, isVarDecl,
         isAppExp, isStrExp, isIfExp, isProcExp, isLetExp, isLitExp, isLetrecExp, isSetExp,
         parseL5Exp, unparse, Exp, parseL5, Program, Parsed } from "../src/L5/L5-ast";
import { Result, bind, mapv, isOkT, makeOk, isFailure, makeFailure, isOk } from "../src/shared/result";
import { parse as parseSexp } from "../src/shared/parser";
import { first, second } from "../src/shared/list";
import { isProcTExp, makeBoolTExp, makeNumTExp, makeProcTExp, makeUnionTExp, parseTExp, unparseTExp } from "../src/L5/TExp";
import { parseTE } from "../src/L5/TExp";


const p = (x: string): Result<Exp> => bind(parseSexp(x), (p) => parseL5Exp(p));

describe('L5 Parser', () => {
    it('parses atomic expressions', () => {
        expect(p("1")).toSatisfy(isOkT(isNumExp));
        expect(p("#t")).toSatisfy(isOkT(isBoolExp));
        expect(p("x")).toSatisfy(isOkT(isVarRef));
        expect(p('"a"')).toSatisfy(isOkT(isStrExp));
        expect(p(">")).toSatisfy(isOkT(isPrimOp));
        expect(p("=")).toSatisfy(isOkT(isPrimOp));
        expect(p("string=?")).toSatisfy(isOkT(isPrimOp));
        expect(p("eq?")).toSatisfy(isOkT(isPrimOp));
        expect(p("cons")).toSatisfy(isOkT(isPrimOp));
    });

    it('parses programs', () => {
        expect(parseL5("(L5 (define x 1) (> (+ x 1) (* x x)))")).toSatisfy(isOkT(isProgram));
    });

    it('parses "define" expressions', () => {
        const def = p("(define x 1)");
        expect(def).toSatisfy(isOkT(isDefineExp));
        if (isOkT(isDefineExp)(def)) {
            expect(def.value.var).toSatisfy(isVarDecl);
            expect(def.value.val).toSatisfy(isNumExp);
        }
    });

    it('parses "define" expressions with type annotations', () => {
        const define = "(define (a : number) 1)";
        expect(p(define)).toSatisfy(isOkT(isDefineExp));
    });

    it('parses applications', () => {
        expect(p("(> x 1)")).toSatisfy(isOkT(isAppExp));
        expect(p("(> (+ x x) (* x x))")).toSatisfy(isOkT(isAppExp));
    });

    it('parses "if" expressions', () => {
        expect(p("(if #t 1 2)")).toSatisfy(isOkT(isIfExp));
        expect(p("(if (< x 2) x 2)")).toSatisfy(isOkT(isIfExp));
    });

    it('parses procedures', () => {
        expect(p("(lambda () 1)")).toSatisfy(isOkT(isProcExp));
        expect(p("(lambda (x) x x)")).toSatisfy(isOkT(isProcExp));
    });

    it('parses procedures with type annotations', () => {
        expect(p("(lambda ((x : number)) : number (* x x))")).toSatisfy(isOkT(isProcExp));
    });

    it('parses "let" expressions', () => {
        expect(p("(let ((a 1) (b #t)) (if b a (+ a 1)))")).toSatisfy(isOkT(isLetExp));
    });

    it('parses "let" expressions with type annotations', () => {
        expect(p("(let (((a : boolean) #t) ((b : number) 2)) (if a b (+ b b)))")).toSatisfy(isOkT(isLetExp));
    });

    it('parses literal expressions', () => {
        expect(p("'a")).toSatisfy(isOkT(isLitExp));
        expect(p("'()")).toSatisfy(isOkT(isLitExp));
        expect(p("'(1)")).toSatisfy(isOkT(isLitExp));
    });

    it('parses "letrec" expressions', () => {
        expect(p("(letrec ((e (lambda (x) x))) (e 2))")).toSatisfy(isOkT(isLetrecExp));
    });

    it('parses "letrec" expressions with type annotations', () => {
        expect(p("(letrec (((p : (number * number -> number)) (lambda ((x : number) (y : number)) (+ x y)))) (p 1 2))")).toSatisfy(isOkT(isLetrecExp));
    });

    it('parses "set!" expressions', () => {
        expect(p("(set! x 1)")).toSatisfy(isOkT(isSetExp));
    });
});

describe('L5 parseTExp Union Parser', () => {
    it('parseTExp parses simple union expressions', () => {
        //todo
        expect(parseTE('(union number boolean)')).toEqual(makeOk({tag: "UnionTExp", comps: [{tag: "BoolTExp"}, { tag: "NumTExp" }]}));
    });

    it('parseTExp parses embedded union expressions', () => {
        // todo
        expect(parseTE('(union number (union string boolean))')).toEqual(makeOk(({tag: "UnionTExp", comps: [{tag: "BoolTExp"}, {tag: "NumTExp"}, {tag: "StrTExp"}]})));

    });

    it('parseTExp parses union types in proc argument position', () => {
        // todo
        expect(parseTE("((union boolean number) -> number)")).toEqual(makeOk(makeProcTExp([makeUnionTExp(makeBoolTExp(), makeNumTExp())], makeNumTExp())));
        
    });
    it('parseTExp parses union types in return type argument position', () => {
        // todo
        expect(parseTE("(number -> (union boolean number))")).toEqual(makeOk(makeProcTExp([makeNumTExp()], makeUnionTExp(makeBoolTExp(), makeNumTExp()))));
    });
    it('parseTExp fails to parse union of bad type expressions', () => {
        // todo
        expect(parseTE('(union a b)')).toSatisfy(isFailure);
    });

});

describe('L5 parse with unions', () => {
    // parse, unparse, remove-whitespace
    const roundTrip = (x: string): Result<string> => 
        bind(parseL5(x), (p: Program) =>
            mapv(unparse(p), (s: string) => 
                s.replace(/\s/g, "")));

    // Compare original string with round-trip (neutralizes white spaces)
    const testProgram = (x: string): Result<void> =>
            mapv(roundTrip(x), (rt: string) => {
                expect(x.replace(/\s/g, "")).toEqual(rt);
            });
    
    it('unparses union of atomic types in different positions: define, let, param, return types', () => {
        const dt1 = `
        (L5 
        )
        `;
        testProgram(dt1);
    });

    it('parses nested union expressions', () => {
        const dt2 = `
        (L5 
        )
        `;
        testProgram(dt2);
    });

});


describe('L5 Unparse', () => {
    const roundTrip = (x: string): Result<string> => bind(p(x), unparse);
    const roadTripForTExp = (x: string): Result<string> =>bind(parseTE(x), unparseTExp);

    it('unparses "define" expressions with type annotations', () => {
        const define = "(define (a : number) 1)";
        expect(roundTrip(define)).toEqual(makeOk(define));
    });

    it('unparses procedures with type annotations', () => {
        const lambda = "(lambda ((x : number)) : number (* x x))";
        expect(roundTrip(lambda)).toEqual(makeOk(lambda));
    });

    it('unparses "let" expressions with type annotations', () => {
        const let1 = "(let (((a : boolean) #t) ((b : number) 2)) (if a b (+ b b)))";
        expect(roundTrip(let1)).toEqual(makeOk(let1));
    });

    it('unparses "letrec" expressions', () => {
        const letrec = "(letrec (((p : (number * number -> number)) (lambda ((x : number) (y : number)) (+ x y)))) (p 1 2))";
        expect(roundTrip(letrec)).toEqual(makeOk(letrec));
    });

    it('unparses union, nested unions in different positions', () => {
        // TODO
        const goodSingleUnion = '(union number boolean)';
        expect(roadTripForTExp(goodSingleUnion)).toEqual(makeOk('(union boolean number)'));
        const nestedUnion1 = '(union string (union number boolean))';
        expect(roadTripForTExp(nestedUnion1)).toEqual(makeOk("(union boolean (union number string))"));

    })
});
