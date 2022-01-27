
module TestParser(tests) where

import Test(Test(..))

import Error(Error(..), ErrorType(..))
import Syntax.Name(QName(..), primitiveUnderscore, primitiveListNil, primitiveListCons)
import Syntax.AST(AnnProgram(..), AnnDeclaration(..),
                  AnnSignature(..), Signature,
                  AnnEquation(..), Equation,
                  AnnConstraint(..), Constraint,
                  AnnCaseBranch(..), CaseBranch,
                  AnnExpr(..), Expr,
                  eraseAnnotations)
import Lexer.Lexer(tokenize)
import Parser.Parser(parse)

testProgram :: String -> String -> Either ErrorType (AnnProgram ()) -> Test
testProgram description source expected =
  TestCase description 
           (normalizeResult
             (do tokens <- tokenize "test" source
                 parse tokens))
           expected
  where
    normalizeResult (Left  e) = Left (errorType e)
    normalizeResult (Right x) = Right (eraseAnnotations x)

testProgramOK :: String -> String -> AnnProgram () -> Test
testProgramOK description source expected =
  testProgram description source (Right expected)

testProgramError :: String -> String -> ErrorType -> Test
testProgramError description source expected =
  testProgram description source (Left expected)

----

testExpr :: String -> String -> Either ErrorType (AnnExpr ()) -> Test
testExpr description source expected =
  TestCase description 
           (normalizeResult (tokenize "test" source >>= parse))
           expected
  where
    normalizeResult (Left  e) = Left (errorType e)
    normalizeResult (Right p) =
      Right (eraseAnnotations
              (equationRHS
                (declEquation (last (programDeclarations p)))))

testExprOK :: String -> String -> AnnExpr () -> Test
testExprOK description source expected =
  testExpr description source (Right expected)

testExprError :: String -> String -> ErrorType -> Test
testExprError description source expected =
  testExpr description source (Left expected)

----

qmain :: String -> QName
qmain x = Qualified "Main" (Name x)

qprim :: String -> QName
qprim x = Qualified "PRIM" (Name x)

primvar :: String -> AnnExpr ()
primvar x = EVar () (qprim x)

evar :: String -> AnnExpr ()
evar x = EVar () (qmain x)

eint :: Integer -> AnnExpr ()
eint n = EInt () n

eapp :: AnnExpr () -> [AnnExpr ()] -> AnnExpr ()
eapp f []       = f
eapp f (x : xs) = eapp (EApp () f x) xs

tests :: Test
tests = TestSuite "PARSER" [

  TestSuite "Declarations" [

    TestSuite "Module declarations" [

      testProgramError "Expect module name after module keyword"
         "module module" 
         ParseErrorExpectedId

    ],

    TestSuite "Type declarations" [

      testProgramOK "Single type declaration"
         (unlines [
           "type Name = String"
         ])
         (Program [
           TypeDeclaration ()
             (evar "Name")
             (EVar () (qprim "String"))
         ]),

      testProgramOK "Type declaration"
         (unlines [
           "type Ages = LST Integer"
         ])
         (Program [
           TypeDeclaration ()
             (evar "Ages")
             (eapp (evar "LST") [evar "Integer"])
         ]),

      testProgramError "Invalid type declaration with no head variable"
         (unlines [
           "type 10 = 10"
         ])
         ParseErrorTypeHasNoHead

    ],

    TestSuite "Data declarations" [

      testProgramOK "Empty data declaration"
         (unlines [
           "data Empty where"
         ])
         (Program [
           DataDeclaration ()
             (evar "Empty")
             []
         ]),

      testProgramOK "Single data declaration"
         (unlines [
           "data Unit where",
           "  tt : Unit"
         ])
         (Program [
           DataDeclaration ()
             (evar "Unit")
             [
               Signature () (qmain "tt") (evar "Unit") []
             ]
         ]),

      testProgramOK "Data declaration"
         (unlines [
           "data Bool where",
           "  True  : Bool",
           "  False : Bool"
         ])
         (Program [
           DataDeclaration ()
             (evar "Bool")
             [
               Signature () (qmain "True") (evar "Bool") [],
               Signature () (qmain "False") (evar "Bool") []
             ]
         ]),

      testProgramError "Invalid data declaration with no head variable"
         (unlines [
           "data 10 where"
         ])
         ParseErrorDataHasNoHead

    ],

    TestSuite "Class declarations" [

      testProgramOK "Empty class declaration"
         (unlines [
           "class Eq a where"
         ])
         (Program [
           ClassDeclaration ()
             (qmain "Eq")
             (qmain "a")
             []
         ]),

      testProgramOK "Class declaration (typical)"
         (unlines [
           "class A b where",
           " f : a",
           " g : b"
         ])
         (Program [
           ClassDeclaration ()
             (qmain "A")
             (qmain "b")
             [
               Signature () (qmain "f") (evar "a") [],
               Signature () (qmain "g") (evar "b") []
             ]
         ]),

      testProgramOK "Class declaration with constraints"
         (unlines [
           "class A b where",
           " f : a   {Eq a; Ord a}",
           " g : b   {Ord b}"
         ])
         (Program [
           ClassDeclaration ()
             (qmain "A")
             (qmain "b")
             [
               Signature () (qmain "f") (evar "a") [
                 Constraint () (qmain "Eq") (qmain "a"),
                 Constraint () (qmain "Ord") (qmain "a")
               ],
               Signature () (qmain "g") (evar "b") [
                 Constraint () (qmain "Ord") (qmain "b")
               ]
             ]
         ]),

      testProgramError "Invalid class declaration"
         (unlines [
           "class Eq where"
         ])
         ParseErrorExpectedId

    ],

    TestSuite "Instance declarations" [

      testProgramOK "Empty instance declaration"
         (unlines [
           "instance Eq Bool where"
         ])
         (Program [
           InstanceDeclaration ()
             (qmain "Eq")
             (evar "Bool")
             []
             []
         ]),

      testProgramOK "Instance declaration (typical)"
         (unlines [
           "instance Eq Bool where",
           "  a = b",
           "  c = d"
         ])
         (Program [
           InstanceDeclaration ()
             (qmain "Eq")
             (evar "Bool")
             []
             [
               Equation () (evar "a") (evar "b"),
               Equation () (evar "c") (evar "d")
             ]
         ]),

      testProgramOK "Instance declaration with constraints"
         (unlines [
           "instance Eq (LST a) {Eq a} where",
           "  c = d"
         ])
         (Program [
           InstanceDeclaration ()
             (qmain "Eq")
             (eapp (evar "LST") [evar "a"])
             [
               Constraint () (qmain "Eq") (qmain "a")
             ]
             [
               Equation () (evar "c") (evar "d")
             ]
         ])

    ],

    TestSuite "Type signatures" [

      testProgramOK "Type signature with constraint"
         (unlines [
           "f : a    {Eq a}"
         ])
         (Program [
           TypeSignature
             (Signature () (qmain "f") (evar "a")
                           [Constraint () (qmain "Eq") (qmain "a")])
         ]),

      testProgramError "Invalid type signature with no head variable"
         (unlines [
           "data Bool where",
           "10 : Bool"
         ])
         ModuleSystemError

    ],

    TestSuite "Value declarations" [

      testProgramError "Invalid value declaration with no head variable"
         (unlines [
           "10 = 10"
         ])
         ParseErrorEquationHasNoHead

    ]

  ],

  TestSuite "Expressions" [

    TestSuite "Variables" [

      testExprOK "Variable"
         "x = y" 
         (evar "y"),

      testExprOK "Variable (underscore)"
         "x = _" 
         (EVar () primitiveUnderscore)

    ],

    TestSuite "Constants" [

      testExprOK "Integer constant"
         "x = 42" 
         (EInt () 42),

      testExprOK "Character constant"
         "x = 'a'" 
         (EChar () 'a'),

      testExprOK "String constant"
         "x = \"abc\""
         (EApp () (EApp () (EVar () primitiveListCons) (EChar () 'a')) (
           (EApp () (EApp () (EVar () primitiveListCons) (EChar () 'b')) (
              (EApp () (EApp () (EVar () primitiveListCons) (EChar () 'c')) (
                (EVar () primitiveListNil)))))))
    ],

    TestSuite "Mixfix operators" [

      testExprError "Reject infix declaration without precedence"
         (unlines [
           "infix foo_",
           "x = foo_"
         ])
         ParseErrorExpectedInt,

      testExprError "Reject using operator part as variable"
         (unlines [
           "infix 20 foo_",
           "x = foo"
         ])
         ParseErrorPrematureEndOfExpression,

      testExprOK "Basic prefix operator"
         (unlines [
           "infix 20 a_",
           "x = a 10"
         ])
         (eapp (evar "a_") [eint 10]),

      testExprOK "Basic suffix operator"
         (unlines [
           "infix 20 _!",
           "x = 10 !"
         ])
         (eapp (evar "_!") [eint 10]),

      testExprOK "Basic infix operator"
         (unlines [
           "infix 20 _++_",
           "x = 10 ++ 20"
         ])
         (eapp (evar "_++_") [eint 10, eint 20]),

      testExprOK "Basic circumfix operator"
         (unlines [
           "infix 20 [[_]]",
           "x = [[ z ]]"
         ])
         (eapp (evar "[[_]]") [evar "z"]),

      testExprOK "Nested infix operators"
         (unlines [
           "infix 20 _+_",
           "infix 30 _*_",
           "infix 40 _^_",
           "x = 1 ^ 2 * 3 ^ 4 + 5 ^ 6 * 7 ^ 8"
         ])
         (eapp (evar "_+_") [
           eapp (evar "_*_") [
             eapp (evar "_^_") [EInt () 1, EInt () 2],
             eapp (evar "_^_") [EInt () 3, EInt () 4]
           ],
           eapp (evar "_*_") [
             eapp (evar "_^_") [EInt () 5, EInt () 6],
             eapp (evar "_^_") [EInt () 7, EInt () 8]
           ]
         ]),

      testExprOK "Parentheses"
         (unlines [
           "infix 20 _+_",
           "infix 30 _*_",
           "infix 40 _^_",
           "x = ((1 + 2) * (3 + 4)) ^ ((5 + 6) * (7 + 8))"
         ])
         (eapp (evar "_^_") [
           eapp (evar "_*_") [
             eapp (evar "_+_") [EInt () 1, EInt () 2],
             eapp (evar "_+_") [EInt () 3, EInt () 4]
           ],
           eapp (evar "_*_") [
             eapp (evar "_+_") [EInt () 5, EInt () 6],
             eapp (evar "_+_") [EInt () 7, EInt () 8]
           ]
         ]),

      testExprOK "Mixed nested operators"
         (unlines [
           "infix 20 foo_bar_baz_",
           "infix 30 _!!",
           "infix 40 ??_",
           "x = ??(foo ?? 1 bar ?? 2 !! baz 3 !!)"
         ])
         (eapp (evar "??_") [
            eapp (evar "foo_bar_baz_") [
              eapp (evar "??_") [eint 1],
              eapp (evar "_!!") [eapp (evar "??_") [eint 2]],
              eapp (evar "_!!") [eint 3]
            ]
          ]),

      testExprError "Reject associating non-associative operator"
         (unlines [
           "infix 20 _+_",
           "x = 1 + 2 + 3"
         ])
         ParseErrorExpectedToken,

      testExprOK "Basic left-associative operator"
         (unlines [
           "infixl 20 _+_",
           "x = 1 + 2 + 3"
         ])
         (eapp (evar "_+_") [
            eapp (evar "_+_") [eint 1, eint 2],
            eint 3
          ]),

      testExprOK "Basic right-associative operator"
         (unlines [
           "infixr 20 _+_",
           "x = 1 + 2 + 3"
         ])
         (eapp (evar "_+_") [
            eint 1,
            eapp (evar "_+_") [eint 2, eint 3]
          ]),

      testExprOK "Operator with default associativity/precedence"
         (unlines [
           "_+_ : a",
           "x = 1 + 2"
         ])
         (eapp (evar "_+_") [
            eint 1,
            eint 2
          ])

    ],

    TestSuite "Application" [

      testExprOK "Nested applications"
         (unlines [
           "x = f (g y) (h a b)"
         ])
         (eapp (evar "f") [
               (eapp (evar "g") [evar "y"]),
               (eapp (evar "h") [evar "a", evar "b"])
         ])

    ],

    TestSuite "Lambda" [

      testExprOK "Empty lambda"
         (unlines [
           "x = \\ -> a"
         ])
         (evar "a"),

      testExprOK "One parameter"
         (unlines [
           "x = \\ a -> b"
         ])
         (ELambda () (evar "a") (evar "b")),

      testExprOK "Many parameters"
         (unlines [
           "x = \\ f g x -> f g x"
         ])
         (ELambda () (evar "f")
           (ELambda () (evar "g")
             (ELambda () (evar "x")
               (eapp (evar "f") [evar "g", evar "x"])))),

      testExprOK "With patterns"
         (unlines [
           "x = \\ (Cons x xs) (Cons y ys) -> a"
         ])
         (ELambda () (eapp (evar "Cons") [evar "x", evar "xs"])
           (ELambda () (eapp (evar "Cons") [evar "y", evar "ys"])
             (evar "a"))),

      testExprOK "Nested lambdas"
         (unlines [
           "x = \\ x -> \\ y -> \\ z -> z y x"
         ])
         (ELambda () (evar "x")
          (ELambda () (evar "y")
            (ELambda () (evar "z") (eapp (evar "z") [evar "y", evar "x"]))))

    ],

    TestSuite "Let" [

      testExprOK "Empty let"
         (unlines [
           "x = let in a"
         ])
         (ELet () [] (evar "a")),

      testExprOK "Let without braces, 'in' on same line"
         (unlines [
           "x = let a = b in c"
         ])
         (ELet ()
           [
             ValueDeclaration (Equation () (evar "a") (evar "b"))
           ]
           (evar "c")),

      testExprOK "Let without braces, 'in' on different line"
         (unlines [
           "x = let a = b",
           "        c = d",
           "     in e"
         ])
         (ELet ()
           [
             ValueDeclaration (Equation () (evar "a") (evar "b")),
             ValueDeclaration (Equation () (evar "c") (evar "d"))
           ]
           (evar "e")),

      testExprOK "Let with braces, 'in' on same line"
         (unlines [
           "x = let { a = b ; c = d } in e"
         ])
         (ELet ()
           [
             ValueDeclaration (Equation () (evar "a") (evar "b")),
             ValueDeclaration (Equation () (evar "c") (evar "d"))
           ]
           (evar "e")),

      testExprOK "Let with braces, 'in' on different line"
         (unlines [
           "x = let { a = b ; c = d }",
           "   in e"
         ])
         (ELet ()
           [
             ValueDeclaration (Equation () (evar "a") (evar "b")),
             ValueDeclaration (Equation () (evar "c") (evar "d"))
           ]
           (evar "e")),

      testExprOK "Allow type signature"
         (unlines [
           "x = let t : Bool",
           "        t = True",
           "     in t"
         ])
         (ELet ()
           [
             TypeSignature (Signature () (qmain "t") (evar "Bool") []),
             ValueDeclaration (Equation () (evar "t") (evar "True"))
           ]
           (evar "t")),

      testExprError "Reject type declaration"
         (unlines [
           "x = let { type B = Bool }",
           "     in t"
         ])
         ParseErrorExpectedExpression

    ],

    TestSuite "Where" [

      testExprOK "Empty where"
        (unlines [
          "x = y where"
        ])
        (ELet () [] (evar "y")),

      testExprOK "Where with value declaration"
        (unlines [
          "x = f where",
          " f = g"
        ])
        (ELet () [
          ValueDeclaration (Equation () (evar "f") (evar "g"))
         ]
         (evar "f")),

      testExprOK "Allow type signature"
        (unlines [
          "x = f where",
          " f : Bool",
          " f = g"
        ])
        (ELet () [
          TypeSignature (Signature () (qmain "f") (evar "Bool") []),
          ValueDeclaration (Equation () (evar "f") (evar "g"))
         ]
         (evar "f")),

      testExprOK "Nested wheres"
        (unlines [
          "x = f where",
          " f : Bool",
          " f = g where",
          "  g : Bool",
          "  g = True"
        ])
        (ELet () [
          TypeSignature (Signature () (qmain "f") (evar "Bool") []),
          ValueDeclaration (Equation () (evar "f") (ELet () [
            TypeSignature (Signature () (qmain "g") (evar "Bool") []),
            ValueDeclaration (Equation () (evar "g") (evar "True"))
          ] (evar "g")))
        ] (evar "f"))

    ],

    TestSuite "Case" [

      testExprOK "Empty case (no branches)"
        (unlines [
          "x = case a of"
        ])
        (ECase () (evar "a") []),

      testExprOK "One branch"
        (unlines [
          "x = case a of",
          "      NIL -> True"
        ])
        (ECase () (evar "a") [CaseBranch () (evar "NIL") (evar "True")]),

      testExprOK "Two branches"
        (unlines [
          "infix 20 _::_",
          "x = case list of",
          "      NIL       -> True",
          "      (x :: xs) -> False"
        ])
        (ECase () (evar "list") [
          CaseBranch () (evar "NIL") (evar "True"), 
          CaseBranch () (eapp (evar "_::_") [
            (evar "x"), (evar "xs")
          ]) (evar "False")])

    ],

    TestSuite "Fresh" [

      testExprOK "Empty fresh"
        (unlines [
          "x = fresh in x"
        ])
        (evar "x"),

      testExprOK "With a fresh variable"
        (unlines [
          "x = fresh a in b"
        ])
        (EFresh () (qmain "a") (evar "b")),

      testExprOK "Variables on same line, 'in' on same line"
        (unlines [
          "x = fresh a b c in z"
        ])
        (EFresh () (qmain "a")
          (EFresh () (qmain "b")
            (EFresh () (qmain "c")
              (evar "z")))),

      testExprOK "Variables on same line, 'in' on different line"
        (unlines [
          "x = fresh a b c",
          " in z"
        ])
        (EFresh () (qmain "a")
          (EFresh () (qmain "b")
            (EFresh () (qmain "c")
              (evar "z")))),

      testExprOK "Variables on different lines, 'in' on same line"
        (unlines [
          "x = fresh a",
          "          b",
          "          c in z"
        ])
        (EFresh () (qmain "a")
          (EFresh () (qmain "b")
            (EFresh () (qmain "c")
              (evar "z")))),

      testExprOK "Variables on different lines, 'in' on different line"
        (unlines [
          "x = fresh a",
          "          b",
          "          c",
          "         in z"
        ])
        (EFresh () (qmain "a")
          (EFresh () (qmain "b")
            (EFresh () (qmain "c")
              (evar "z"))))

    ]

  ],

  TestSuite "Interaction between parser and module system" [

    testExprOK "Import declared name from module"
       (unlines [
         "module A where",
         "  f : Bool",
         "module B where",
         "  import A",
         "  x = f"
       ])
       (EVar () (Qualified "A" (Name "f"))),

    testExprOK "Import defined name from module"
       (unlines [
         "module A where",
         "  f x y = 1",
         "module B where",
         "  import A",
         "  x = f"
       ])
       (EVar () (Qualified "A" (Name "f"))),

    testExprOK "Import datatype from module"
       (unlines [
         "module A where",
         "  data Bool where",
         "    True : Bool",
         "module B where",
         "  import A",
         "  x = Bool"
       ])
       (EVar () (Qualified "A" (Name "Bool"))),

    testExprOK "Import constructor from module"
       (unlines [
         "module A where",
         "  data Bool where",
         "    True : Bool",
         "module B where",
         "  import A",
         "  x = True"
       ])
       (EVar () (Qualified "A" (Name "True"))),

    testExprOK "Import type from module"
       (unlines [
         "module A where",
         "  type N = Int",
         "module B where",
         "  import A",
         "  x = N"
       ])
       (EVar () (Qualified "A" (Name "N")))

  ],

  TestSuite "More complex tests" [

    testProgramOK "Empty program"
      "" 
      (Program []),

    testProgramOK "Example: list concatenation"
       (unlines [
         "data LST a where",
         "  NIL  : LST a",
         "  _::_ : a -> LST a -> LST a",
         "_++_ : LST a -> LST a -> LST a",
         "NIL       ++ ys = ys",
         "(x :: xs) ++ ys = x :: (xs ++ ys)"
       ])
       (Program [
         DataDeclaration ()
           (eapp (evar "LST") [evar "a"])
           [
             Signature () (qmain "NIL")
                          (eapp (evar "LST") [evar "a"])
                          [],
             Signature () (qmain "_::_")
                          (eapp (primvar "_→_") [
                            evar "a",
                            eapp (primvar "_→_") [
                              eapp (evar "LST") [evar "a"],
                              eapp (evar "LST") [evar "a"]
                            ]
                          ])
                          []
           ],
         TypeSignature (Signature ()
                          (qmain "_++_")
                          (eapp (primvar "_→_") [
                            eapp (evar "LST") [evar "a"],
                            eapp (primvar "_→_") [
                              eapp (evar "LST") [evar "a"],
                              eapp (evar "LST") [evar "a"]
                            ]
                          ])
                          []),
         ValueDeclaration (Equation ()
                            (eapp (evar "_++_") [evar "NIL", evar "ys"])
                            (evar "ys")),
         ValueDeclaration (Equation ()
                            (eapp (evar "_++_") [
                              eapp (evar "_::_") [evar "x", evar "xs"],
                              evar "ys"
                            ])
                            (eapp (evar "_::_") [
                              evar "x",
                              eapp (evar "_++_") [evar "xs", evar "ys"]
                            ]))
       ])

  ]

 ]

