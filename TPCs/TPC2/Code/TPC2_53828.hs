-- This code was written by Gabriel Costa (pg53828@alunos.uminho.pt)

module TPC2_53828 where


------------------------------------------------------------------------------------------------------
------------------- DataTypes needed for the implementation of the while-languge ---------------------
------------------------------------------------------------------------------------------------------

data FTree a b = Tip a 
               | Join b (FTree a b, FTree a b) deriving Show
               
data BoolTree a b = TipB a 
                  | Not (BoolTree a b) 
                  | Leq (FTree a b, FTree a b) 
                  | And (BoolTree a b, BoolTree a b) deriving Show

type Time = Int
type Memory = [(String, Int)]

data Ops = Sum
         | Mult
         deriving Show 

type Term = FTree (Either String Int) Ops

type BoolTerm = BoolTree (Either String Int) Ops

data Prog = Assign String Term
          | Wait Int Prog
          | Seq Prog Prog
          | If BoolTerm Prog Prog
          | While BoolTerm Prog
          | Empty deriving Show


------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------
--------------------------------- Semantics of the while-language ------------------------------------
------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------

-- Quality of life functions, that evaluates a program with an initially empty memory
evaluate :: Prog -> (Time,Memory)
evaluate p = eval (p, [])

-- The eval fucntions recerives an pair (program, Memory) and returns the pair (execution time, updated Memory)
eval :: (Prog,Memory) ->  (Time, Memory)

{-
    If a program as nothing to do, it returns the initial memory with 0 seconds elapsed
-}
eval (Empty,env) = (0,env)

{-
    Assigment rule (asg): Store the value of the term "t" in memory instantaneously.
-}
eval (Assign x t, env) = let env' = update x (evalTerm (t,env)) env
                         in (0, env')

{-
    Wait rule (wait): Evaluates the program "p" after waiting n seconds, returning the total time elapsed and 
    the memory obtained by evaluating the program "p".
-}
eval (Wait n p, env) = (n + n', env') where
    (n', env') = eval (p,env)

{-
    Sequence rule (Seq): Evaluates the program "p1" and then use the memory obtained by this evaluation to evaluate
    the program "p2", returning the total time elapsed and the memory obtained after evaluating "p2".
-}
eval (Seq p1 p2, env) = let (n1,env') = eval (p1,env)
                            (n2,env'') = eval (p2,env')
                        in (n1+n2,env'')

{-
    If rules (if_1 and if_2): If b evaluates to true then the program "p1" is evaluated, else the program "p2" is
    evaluated instead.
-}
eval (If b p1 p2,env) = if evalBoolTerm (b,env) then eval (p1,env) else eval (p2,env)

{-
    While rules (wh_1 and wh_2): If b evaluates to true, then a program "p" is evaluated and the cycle is repeated
    using the memory resulted from the "p" evaluation, returning the total elapsed time (time from evaluating "p" plus
    time for evaluating the new cycle iteration). If b evaluates to false, then the original memory is returned with 0
    seconds elapsed.

-}
eval (While b p,env) = if evalBoolTerm (b,env) then
                                   let (n, env') = eval (p,env)
                                       (m, env'') = eval (While b p, env')
                                   in (m + n, env'')
                                 else
                                    (0, env)

------------------------------------------------------------------------------------------------------
----------------------------------------- Auxiliar Functions -----------------------------------------
------------------------------------------------------------------------------------------------------

{-
    Checks if a variable is present in the Memory. If it is then it's value is returned, else an error is returned 
    instead.
-}
locate :: String -> Memory -> Int
locate _ [] = error "Variable was not previously defined"
locate x ((a,b):t) = if x == a then b else locate x t

-- Function that evaluates a term
evalTerm :: (Term, Memory) -> Int
evalTerm (Tip (Left x) ,s) = locate x s -- if the term is a tree with "Tip variable", then the value of the variable in memory is returned
evalTerm (Tip (Right x) ,s) = x -- if the term is a tree of form "Tip value", then the value is returned
evalTerm (Join Sum (l,r),s) = evalTerm (l,s) + evalTerm (r,s) -- The the tree is a sum of two terms, then each term is evalueted recursively and then summed
evalTerm (Join Mult (l,r),s) = evalTerm (l,s) * evalTerm (r,s) -- Similaryl to the sum, in multiplication, each term is multiplied after being evaluated.

-- Function that evaluates a Boolean term
evalBoolTerm :: (BoolTerm,Memory) -> Bool
evalBoolTerm (TipB (Right x),s) = x /= 0 -- If x is a number, it is consider flase if it is equal to zero, true otherwise
evalBoolTerm (TipB (Left x),s) = locate x s /= 0 -- Similarly to the previous, if x is a variable, if its value equal zero then it evalueted to false, 
                                                 -- true otherwise
evalBoolTerm (Leq (t1,t2),s) = evalTerm (t1,s) <= evalTerm (t2,s) -- Inequality between two terms (lesser or qual)
evalBoolTerm (And (t1,t2),s) = evalBoolTerm (t1,s) && evalBoolTerm (t2,s) -- Conjunction of two terms
evalBoolTerm (Not t,s) = not (evalBoolTerm (t,s)) -- Negation of a boolean term

-- Updates the Memory. Updates the value of a variable if it is in memory, otherwise adds it to the memory
update :: String -> Int -> Memory -> Memory
update varName newVal [] = [(varName,newVal)]
update varName newVal ((memVar,memVal):t) = if varName == memVar then (memVar,newVal):t else (memVar,memVal): update varName newVal t


------------------------------------------------------------------------------------------------------
---------------------------------- Examples of possible programs -------------------------------------
------------------------------------------------------------------------------------------------------

p1 :: Prog
p1 = Assign "x" (Tip (Right 14))
-- evaluation results in: (0,[("x",14)])

p2 :: Prog 
p2 = Seq (Wait 5 (Assign "z" (Join Sum (Tip (Left "x"), Tip (Right (-4)))))) (Wait 7 (Assign "y" (Join Mult (Tip (Left "z"), Tip (Right 4))))) 
-- evaluation results in: (12,[("x",14),("z",10),("y",40)])


p3 :: Prog
p3 = If (Not (Leq (Tip (Left "y"),Tip (Right (-1))))) (Assign "x" (Tip (Right 50))) (Assign "x" (Tip (Right (-50)))) 
-- evaluation results in: (0,[("x",50),("z",10),("y",40)])


p4 :: Prog
p4 = While (Not (Leq (Tip (Left "y"),Tip (Right 0)))) (Wait 5 (Assign "y" (Join Sum (Tip (Left "y"),Tip (Right (-1)))))) 
-- evaluation results in:  (200,[("x",50),("z",10),("y",0)])


p5 :: Prog
p5 = While (And (Not (Leq (Tip (Left "z"),Tip (Right 5))), Not (Leq (Tip (Left "x"),Tip (Right (-50)))))) 
           (Wait 1 (Assign "x" (Join Sum (Tip (Left "x"),Tip (Right (-1))))))
-- evaluation results in: (100,[("x",-50),("z",10),("y",0)])

-- NOTE: The evaluation of each program previously described depends of the evaluation of the one before him.

-- Function that converts a list of programs into a single program, using the sequence rule
foldProg :: [Prog] -> Prog
foldProg = foldr Seq Empty

-- Example of a program containg all the previous programs, built using foldProg function
prog :: Prog
prog = foldProg [p1,p2,p3,p4,p5]
-- evaluation results in: (312,[("x",-50),("z",10),("y",0)]) 

------------------------------------------------------------------------------------------------------
--------------------- Functions that allows a better vizualization of the programs -------------------
------------------------------------------------------------------------------------------------------

help :: IO()
help = putStr $ unlines ["foldProg -> Receives a list of programs and returns the program obtained by applying the Seq rule to it",
                         "printProg -> Receives a program and print's it in a ore pleasent way",
                         "evaluate -> Receives a program and evaluates it with an initially empty memory",
                         "eval -> Receives a program and a memory, and evaluates the program with the given memory"]

-- Converts terms evaluations from Ftrees to its string represntation
termToStr :: Term -> String
termToStr (Tip (Right x)) = show x
termToStr (Tip (Left x)) = x
termToStr (Join Mult (l,r)) = termToStr l ++ " * " ++ termToStr r
termToStr (Join Sum (l,r)) = termToStr l ++ " + " ++ termToStr r

-- Converts boolean terms from BoolTrees to its string representaion
boolTermToStr :: BoolTerm -> String
boolTermToStr (TipB (Right x)) = show x ++ " "
boolTermToStr (TipB (Left x)) = x ++ " "
boolTermToStr (Leq (l,r)) = termToStr l ++ " <= " ++ termToStr r
boolTermToStr (And (l,r)) = boolTermToStr l ++ " && " ++ boolTermToStr r
boolTermToStr (Not t) = "not (" ++ boolTermToStr t ++ ")"

-- Converts a program to its string represntation
programToString :: Prog -> String
programToString Empty = "Program ended\n"
programToString (Assign x t) = x ++ " := " ++ termToStr t
programToString (Wait n p) = "wait " ++ show n  ++ " then {" ++ programToString p ++ "}"
programToString (Seq p1 p2) = programToString p1 ++ "\n" ++ programToString p2
programToString (If b p1 p2) = "If (" ++ boolTermToStr b ++ ") then {" ++ programToString p1 ++ "} else {" ++ programToString p2 ++ "}"
programToString (While b p) = "While (" ++ boolTermToStr b ++ ") do {" ++ programToString p ++ "}"

-- Receives a program and shows its representation, replacing "\n" with new lines
printProg :: Prog -> IO()
printProg p = putStr $ programToString p