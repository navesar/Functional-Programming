import { isProgram, parseL5, parseL5Program, Program, makeStrExp } from '../src/L5/L5-ast';
import { typeofProgram, L5typeof, checkCompatibleType, typeofIf, typeofExp } from '../src/L5/L5-typecheck';
import { applyTEnv, makeEmptyTEnv } from '../src/L5/TEnv';
import { isNumTExp, isProcTExp, makeBoolTExp, makeNumTExp, makeProcTExp, makeTVar, 
         makeVoidTExp, unparseTExp, TExp, isTExp } from '../src/L5/TExp';
import { makeOk, isOkT, bind, mapv, isFailure, Result, makeFailure, isOk } from '../src/shared/result';
import { parseTE, makeStrTExp, makeUnionTExp } from '../src/L5/TExp';
import {parse as p} from "../src/shared/parser";
describe('L5 Type Checker', () => {
    describe('parseTE', () => {
        it('parses atoms', () => {
            expect(parseTE("number")).toEqual(makeOk(makeNumTExp()));
            expect(parseTE("boolean")).toEqual(makeOk(makeBoolTExp()));
        });

        it('parses type variables', () => {
            expect(parseTE("T1")).toEqual(makeOk(makeTVar("T1")));
        });

        it('parses procedures', () => {
            expect(parseTE("(number -> (number -> number))")).toEqual(
                makeOk(makeProcTExp([makeNumTExp()], makeProcTExp([makeNumTExp()], makeNumTExp())))
            );
        });

        it('parses "void" and "Empty"', () => {
            expect(parseTE("void")).toEqual(makeOk(makeVoidTExp()));
            expect(parseTE("(Empty -> void)")).toEqual(makeOk(makeProcTExp([], makeVoidTExp())));
        });
    });

    describe('unparseTExp', () => {
        it('unparses atoms', () => {
            expect(unparseTExp(makeNumTExp())).toEqual(makeOk("number"));
            expect(unparseTExp(makeBoolTExp())).toEqual(makeOk("boolean"));
        });

        it('unparses type variables', () => {
            expect(unparseTExp(makeTVar("T1"))).toEqual(makeOk("T1"));
        });

        it('unparses procedures', () => {
            expect(unparseTExp(makeProcTExp([makeTVar("T"), makeTVar("T")], makeBoolTExp()))).toEqual(makeOk("(T * T -> boolean)"));
            expect(unparseTExp(makeProcTExp([makeNumTExp()], makeProcTExp([makeNumTExp()], makeNumTExp())))).toEqual(makeOk("(number -> (number -> number))"));
        });
    });

    describe('L5typeof', () => {
        it('returns the types of atoms', () => {
            expect(L5typeof("5")).toEqual(makeOk("number"));
            expect(L5typeof("#t")).toEqual(makeOk("boolean"));
        });

        it('returns the type of primitive procedures', () => {
            expect(L5typeof("+")).toEqual(makeOk("(number * number -> number)"));
            expect(L5typeof("-")).toEqual(makeOk("(number * number -> number)"));
            expect(L5typeof("*")).toEqual(makeOk("(number * number -> number)"));
            expect(L5typeof("/")).toEqual(makeOk("(number * number -> number)"));
            expect(L5typeof("=")).toEqual(makeOk("(number * number -> boolean)"));
            expect(L5typeof("<")).toEqual(makeOk("(number * number -> boolean)"));
            expect(L5typeof(">")).toEqual(makeOk("(number * number -> boolean)"));
            expect(L5typeof("not")).toEqual(makeOk("(boolean -> boolean)"));
        });

        it("returns the type of primitive op applications", () => {
            expect(L5typeof("(+ 1 2)")).toEqual(makeOk("number"));
            expect(L5typeof("(- 1 2)")).toEqual(makeOk("number"));
            expect(L5typeof("(* 1 2)")).toEqual(makeOk("number"));
            expect(L5typeof("(/ 1 2)")).toEqual(makeOk("number"));

            expect(L5typeof("(= 1 2)")).toEqual(makeOk("boolean"));
            expect(L5typeof("(< 1 2)")).toEqual(makeOk("boolean"));
            expect(L5typeof("(> 1 2)")).toEqual(makeOk("boolean"));

            expect(L5typeof("(not (< 1 2))")).toEqual(makeOk("boolean"));
        });

        it.skip('type checking of generic functions is not supported', () => {
            // All of these fail in TypeCheck because we do not support generic functions
            // They do work in Type Inference.
            expect(L5typeof("(eq? 1 2)")).toEqual(makeOk("boolean"));
            expect(L5typeof('(string=? "a" "b")')).toEqual(makeOk("boolean"));
            expect(L5typeof('(number? 1)')).toEqual(makeOk("boolean"));
            expect(L5typeof('(boolean? "a")')).toEqual(makeOk("boolean"));
            expect(L5typeof('(string? "a")')).toEqual(makeOk("boolean"));
            expect(L5typeof('(symbol? "a")')).toEqual(makeOk("boolean"));
            expect(L5typeof('(list? "a")')).toEqual(makeOk("boolean"));
            expect(L5typeof('(pair? "a")')).toEqual(makeOk("boolean"));
        });

        it('returns the type of "if" expressions', () => {
            expect(L5typeof("(if (> 1 2) 1 2)")).toEqual(makeOk("number"));
            expect(L5typeof("(if (= 1 2) #t #f)")).toEqual(makeOk("boolean"));
        });

        it('returns the type of procedures', () => {
            expect(L5typeof("(lambda ((x : number)) : number x)")).toEqual(makeOk("(number -> number)"));
            expect(L5typeof("(lambda ((x : number)) : boolean (> x 1))")).toEqual(makeOk("(number -> boolean)"));
            expect(L5typeof("(lambda((x : number)) : (number -> number) (lambda((y : number)) : number (* y x)))")).toEqual(makeOk("(number -> (number -> number))"));
            expect(L5typeof("(lambda((f : (number -> number))) : number (f 2))")).toEqual(makeOk("((number -> number) -> number)"));
            expect(L5typeof("(lambda((x : number)) : number (let (((y : number) x)) (+ x y)))")).toEqual(makeOk("(number -> number)"));
        });

        it('returns the type of "let" expressions', () => {
            expect(L5typeof("(let (((x : number) 1)) (* x 2))")).toEqual(makeOk("number"));
            expect(L5typeof("(let (((x : number) 1) ((y : number) 3)) (+ x y))")).toEqual(makeOk("number"));
            expect(L5typeof("(let (((x : number) 1) ((y : number) 2)) (lambda((a : number)) : number (+ (* x a) y)))")).toEqual(makeOk("(number -> number)"));
        });

        it('returns the type of "letrec" expressions', () => {
            expect(L5typeof("(letrec (((p1 : (number -> number)) (lambda((x : number)) : number (* x x)))) p1)")).toEqual(makeOk("(number -> number)"));
            expect(L5typeof("(letrec (((p1 : (number -> number)) (lambda((x : number)) : number (* x x)))) (p1 2))")).toEqual(makeOk("number"));
            expect(L5typeof(`
                (letrec (((odd? : (number -> boolean)) (lambda((n : number)) : boolean (if (= n 0) #f (even? (- n 1)))))
                         ((even? : (number -> boolean)) (lambda((n : number)) : boolean (if (= n 0) #t (odd? (- n 1))))))
                  (odd? 12))`)).toEqual(makeOk("boolean"));
        });

        it('returns "void" as the type of "define" expressions', () => {
            expect(L5typeof("(define (foo : number) 5)")).toEqual(makeOk("void"));
            expect(L5typeof("(define (foo : (number * number -> number)) (lambda((x : number) (y : number)) : number (+ x y)))")).toEqual(makeOk("void"));
            expect(L5typeof("(define (x : (Empty -> number)) (lambda () : number 1))")).toEqual(makeOk("void"));
        });

        it.skip('returns "literal" as the type for literal expressions', () => {
            expect(L5typeof("(quote ())")).toEqual(makeOk("literal"));
        });
	});
    const programTest2 = (concreteExp: string): Result<string> =>
        bind(p(concreteExp), (x) =>
            bind(parseL5Program(x), (e: Program) =>
                bind(typeofExp(e, makeEmptyTEnv()), unparseTExp)));
    // TODO L51 Typecheck program with define
    describe('L5 Typecheck program with define', () => {
        // TODO L51
        it('returns ok/failure to define type', () => {
            expect(L5typeof("(define (x : boolean) 3)")).toSatisfy(isFailure);
            expect(L5typeof("(define (z : number) 3)")).toEqual(makeOk("void"));
            expect(L5typeof("(define (w : string) 3)")).toSatisfy(isFailure);
        });
        it('returns the type of program without define', () => {
            expect(programTest2("(L5 (+ 3 4))")).toEqual(makeOk("number"));
            expect(programTest2("(L5 #t)")).toEqual(makeOk("boolean"));
        });
        it('returns "t" as the type of program with define is t', () => {
            expect(programTest2("(L5 (define (y : number) 5) y)")).toEqual(makeOk("number"));
            expect(programTest2("(L5 (define (foo : (number * number -> number)) (lambda((x : number) (y : number)) : number (+ x y))) foo)")).toEqual(makeOk("(number * number -> number)"));
        });
    });

    // TODO L51 Test checkCompatibleType with unions
    describe('L5 Test checkCompatibleType with unions', () => {
        // TODO L51
        it('checks compatible type', () => {
            const T2 = parseTE("(union number boolean)");
            const T1 = parseTE("number");
            if (isOk(T1) && isOk(T2)) {
                const result = checkCompatibleType(T2.value, T1.value, makeStrExp("testExp"))
                const isFailed = result.tag == 'Failure';
                expect(checkCompatibleType(T1.value, T2.value, makeStrExp("testExp"))).toEqual(makeOk(true));
                expect(isFailed).toEqual(true);
            }
        });
        it('checks if two compatible types are equal', () => {
            expect(checkCompatibleType(makeUnionTExp(makeNumTExp(), makeBoolTExp()), makeUnionTExp(makeNumTExp(), makeBoolTExp()), makeStrExp("testExp"))).toEqual(makeOk(true));
            const result = checkCompatibleType(makeUnionTExp(makeNumTExp(), makeBoolTExp()), makeUnionTExp(makeNumTExp(), makeStrTExp()), makeStrExp("testExp"))
            const isFailed = result.tag == 'Failure';
            expect(isFailed).toEqual(true);
            expect(checkCompatibleType(makeUnionTExp(makeNumTExp(), makeBoolTExp()), makeUnionTExp(makeStrTExp(), makeUnionTExp(makeBoolTExp(), makeNumTExp())), makeStrExp("testExp"))).toEqual(makeOk(true));
        });
    });

    // TODO L51 Test makeUnion
    describe('L5 Test makeUnion', () => {
        // makeUnion( number, boolean) -> union((number, boolean))
        // makeUnion( union(number, boolean), string) -> union(boolean, number, string)
        // makeUnion( union(number, boolean), union(boolean, string)) -> union(boolean, number, string)
        // makeUnion( number, union(number, boolean)) -> union(boolean, number)
     
        // TODO L51
        //we tested it in ast.test
    });
    
    // TODO L51 Test typeOfIf with union in all relevant positions
    describe('L5 Test typeOfIf with union in all relevant positions', () => {
        // typeOfIf( (if #t 1 #t) ) -> union(boolean, number)
        // typeOfIf( (if #t 1 2) ) -> number
        // typeOfIf( (if #t (if #f 1 #t) "ok") ) -> union(boolean, number, string)
        // typeOfIf( (if 1 2 3) ) -> failure
        expect(L5typeof("(if #t 1 #t)")).toEqual(makeOk( "(union boolean number)"));
        expect(L5typeof("(if #t 1 2)")).toEqual(makeOk( "number"));
        expect(L5typeof('(if #t (if #f 1 #t) "ok")')).toEqual(makeOk("(union boolean (union number string))"));
        expect(L5typeof("(if 1 2 3)")).toEqual(makeFailure("Incompatible types: number and boolean in (if 1 2 3)"));
        
    });

    // TODO L51 Test checkCompatibleType with unions in arg positions of Procedures
    describe('L5 Test checkCompatibleType with unions in arg positions of Procedures', () => {
        // TODO L51
        // Implement the test for the examples given in the document of the assignment (3.2.4)\
        it('checks compatible type with unions in arg positions of procedures', () => {
            const T2 = parseTE("(number -> (union number boolean))");
            const T1 = parseTE("(number -> number)");

            if (isOk(T1) && isOk(T2)) {
                const result = checkCompatibleType(T2.value, T1.value, makeStrExp("testExp"))
                const isFailed = result.tag == 'Failure';
                expect(checkCompatibleType(T1.value, T2.value, makeStrExp("testExp"))).toEqual(makeOk(true));
                expect(isFailed).toEqual(true);
            }
        })
    });

});
