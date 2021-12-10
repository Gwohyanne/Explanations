import Data.Text.Internal.Builder.Functions (i2d)
import Data.Fixed (E2)
import Data.List
import Language.Haskell.TH (match, valD)
import Distribution.Simple.LocalBuildInfo (withAllComponentsInBuildOrder)
import Distribution.Simple.Command (OptDescr(BoolOpt))
import GHC.Windows (failWith)
import Control.Applicative.Lift (failure)
import Text.XHtml (HtmlTree)

-- type definitions
data Value = Int | String 
data Index = Index {name :: String,
                    variation :: Int} deriving Eq

instance Show Index where
    show i | variation i == 0 = name i
    show i = name i ++ show (variation i)

data Scope = All Index | Each Index | One | AllButOne Index | ExistsOne Index
instance Show Scope where
    show (All i) = "pour tout " ++ show i
    show (Each i) = "pour " ++ show i
    show One = ""
    show (AllButOne i) = "pour tout " ++ show i ++ " différent de précédent!" ++ show i
    show (ExistsOne i) = "il existe " ++ show i ++ " tel que"
instance Eq Scope where
    All i1 == All i2 = i1==i2
    Each i1 == Each i2 = i1==i2
    _ == _ = False

data Element = Var (String, [Index]) | ReiVar (String, [Index]) | Ind Index | Not Element | Val Integer
instance Show Element where
    show (Var (s, i)) = s ++ "_" ++ concatMap show i ++ " "
    show (ReiVar (s, i)) = s ++ "_" ++ concatMap show i ++ " "
    show (Ind i) = show i 
    show (Not e) = "non-" ++ show e 
    show (Val v) = show v
instance Eq Element where
    Var (s1, i1) == Var (s2, i2) = s1==s2 && i1==i2
    ReiVar (s1, i1) == ReiVar (s2, i2) = s1==s2 && i1==i2
    Ind i1 == Ind i2 = i1==i2
    Not e1 == Not e2 = e1==e2
    Val v1 == Val v2 = v1==v2
    _ == _ = False
-- not sure Or and And are useful
-- $dShow :: Show a

data Event a = Equ (a, a) | Leq (a, a) | Geq (a, a) | Or [a] | And [a] | Only a | None
instance Show a => Show (Event a) where
    show (Equ (a1, a2)) = show a1 ++ "= " ++ show a2
    show (Leq (a1, a2)) = show a1 ++ "<= " ++ show a2
    show (Geq (a1, a2)) = show a1 ++ ">= " ++ show a2
    show (Or a) = "BigVee" ++ show a
    show (And a) = "BidWedge" ++ show a
    show (Only a) = show a
    show None = "NONE"
instance Eq a => Eq (Event a) where
    Equ (a, b) == Equ (c, d) = (a==c && b==d)||(a==d && b==c)
    Leq (a, b) == Leq (c, d) = (a==c && b==d)||(a==d && b==c)
    Geq (a, b) == Geq (c, d) = (a==c && b==d)||(a==d && b==c)
    Or a == Or b = a==b
    And a == And b = a==b
    Only a == Only b = a==b
    None == None = True
    _ == _ = False
type DecomposedConstraint = (Integer, [Scope], [Event Element])
--instance Eq DecomposedConstraint where
--    (i1, s1, e1) == (i2, s2, e2) = i1==i2 && s1==s2 && e1==e2 
--    _ == _ = False
type GlobalConstraint = [DecomposedConstraint]

data Tree = Lit (Event Element, Scope) | OR (Event Element, Scope, [Tree]) | AND (Event Element, Scope, [Tree])

instance Show Tree where
    show (Lit (None, _)) = "NONE"
    show (Lit (e, One)) = show e 
    show (Lit (e, s)) = show s ++ ", " ++ show e
    show (OR(e, One, t:ts)) = show e ++ "---> [" ++ show t ++ concatMap (\x -> " ou " ++ show x) ts ++ "]"
    show (OR(e, s, t:ts)) = show s ++ ", " ++ show e ++ "---> [" ++ show t ++ concatMap (\x -> " ou " ++ show x) ts ++ "]"
    show (OR(_, _, _)) = "OR ISSUE"
    show (AND(e, One, t:ts)) = show e ++ "---> [" ++ show t ++ concatMap (\x -> " ou " ++ show x) ts ++ "]"
    show (AND(e, s, t:ts)) = show s ++ ", " ++ show e ++ "---> [" ++ show t ++ concatMap (\x -> " ou " ++ show x) ts ++ "]"
    show (AND(_, _, _)) = "AND ISSUE"

-- research functions
positiveElement :: Element -> Element
positiveElement (Not e) = e
positiveElement e = e

negativeElement :: Element -> Element
negativeElement (Not e) = (Not e)
negativeElement e = (Not e)

getElements :: Event Element -> [Element]
getElements (Equ (e1, e2)) = [positiveElement e1, positiveElement e2]
getElements (Leq (e1, e2)) = [positiveElement e1, positiveElement e2]
getElements (Geq (e1, e2)) = [positiveElement e1, positiveElement e2]
getElements (Or e) = map positiveElement e
getElements (And e) = map positiveElement e
getElements (Only e) = [positiveElement e]
getElements None = []

getNeutralElements :: Event Element -> [Element]
getNeutralElements (Equ (e1, e2)) = [e1, e2]
getNeutralElements (Leq (e1, e2)) = [e1, e2]
getNeutralElements (Geq (e1, e2)) = [e1, e2]
getNeutralElements (Or e) = e
getNeutralElements (And e) = e
getNeutralElements (Only e) = [e]
getNeutralElements None = []

getElementSignature :: Element -> Bool 
getElementSignature (Not _) = False 
getElementSignature _ = True

getEventSignature :: Event Element -> Bool 
getEventSignature es = foldr ((&&) . getElementSignature) True (getNeutralElements es)

getElementName :: Element -> String
getElementName (Var (s, _)) = s 
getElementName (ReiVar (s, _)) = s 
getElementName (Ind s) = name s 
getElementName (Not e) = getElementName e
getElementName (Val v) = ""

negateElement :: Element -> Element
negateElement (Not e) = e 
negateElement e = Not e

getScopeAllIndices :: [Scope] -> [Index]
getScopeAllIndices ((All i):sl) = i : getScopeAllIndices sl
getScopeAllIndices ((Each i): sl) = getScopeAllIndices sl
getScopeAllIndices [] = [] 

getScopeFromDC :: DecomposedConstraint -> [Scope]
getScopeFromDC (_, s, _) = s

getElementIndices :: Element -> [Index]
getElementIndices (Var (_, i)) = i 
getElementIndices (ReiVar (_, i)) = i 
getElementIndices (Ind i) = [i]
getElementIndices (Not e) = getElementIndices e 

getEventIndices :: [Element] -> [Index]
getEventIndices = concatMap getElementIndices

negateEvent :: Event Element -> Event Element
negateEvent (Equ (e1, e2)) = Equ (negateElement e1, e2)
negateEvent (Leq (e1, e2)) = Leq (negateElement e1, e2)
negateEvent (Geq (e1, e2)) = Geq (negateElement e1, e2)
negateEvent (Or e) = undefined
negateEvent (And e) = undefined 
negateEvent (Only e) = Only (negateElement e)
negateEvent None = None

getEventsFromDC :: DecomposedConstraint -> [Event Element]
getEventsFromDC (_, _, c) = c

findAllIndex :: DecomposedConstraint -> Index
findAllIndex (_, (All i):xs, _) = i 
findAllIndex (e, _:xs, s) = findAllIndex (e, xs, s)
findAllIndex (e, [], s) = error "No All Index"

elementIsInList :: [Element] -> Element -> Bool 
elementIsInList (l:ls) e | getElementName l == getElementName e = True
                        | otherwise = elementIsInList ls e
elementIsInList [] e = False

findEventInGC :: GlobalConstraint -> Event Element -> [DecomposedConstraint]
findEventInGC (c:cs) e | foldr ((&&) . (elementIsInList (concatMap getElements (getEventsFromDC c)))) True (getElements e) = c : (findEventInGC cs e)
                       | otherwise = findEventInGC cs e
findEventInGC [] e = []

isReified :: Element -> Bool
isReified (ReiVar r) = True
isReified _ = False

findReifiedElement :: [Element] -> Bool
findReifiedElement (e:es) | isReified e = True
                          | otherwise = findReifiedElement es
findReifiedElement [] = False

findReifiedEvent :: [Event Element] -> Event Element
findReifiedEvent (e:es) | findReifiedElement (getElements e) = e 
                        | otherwise = findReifiedEvent es 
findReifiedEvent [] = None

findNonReifiedElement :: [Element] -> Bool
findNonReifiedElement (e:es) | isReified e = findNonReifiedElement es
                             | otherwise = True
findNonReifiedElement [] = False

findNonReifiedEvent :: [Event Element] -> Bool -> Event Element
findNonReifiedEvent (e:es) b | findNonReifiedElement (getElements e) && b = e
                             | findNonReifiedElement (getElements e) && not b = negateEvent e
                             | otherwise = findNonReifiedEvent es b 
findNonReifiedEvent [] b = None

searchAndRemoveElement :: Element -> [Element] -> [Event Element]
searchAndRemoveElement _ [] = []
searchAndRemoveElement e (l:ls) | positiveElement e == l || negativeElement e == l = searchAndRemoveElement e ls
                                | otherwise = Only l : searchAndRemoveElement e ls

removeFromDC :: Event Element -> [Event Element] -> [Event Element]
removeFromDC (Only (Not e)) (l:ls) = searchAndRemoveElement e (map negateElement (getNeutralElements l)) ++ removeFromDC (Only e) ls
removeFromDC (Only e) (l:ls) = searchAndRemoveElement e (getNeutralElements l) ++ removeFromDC (Only e) ls
removeFromDC e s = delete e s

isMultipleInstances :: Event Element -> DecomposedConstraint -> Bool
isMultipleInstances e (_, s, _) = let i = getEventIndices (getElements e) in
    let si = getScopeAllIndices s in
    search i si
    where search :: [Index] -> [Index] -> Bool
          search (i:is) si | elem i si = True 
                         | otherwise = search is si 
          search [] _ = False

removeDCFromGC :: DecomposedConstraint -> GlobalConstraint -> GlobalConstraint
removeDCFromGC _ [] = []
removeDCFromGC (n, a, b) ((m, c, d):gs) | n == m = removeDCFromGC (n, a, b) gs
                                        | otherwise = (m, c, d) : removeDCFromGC (n, a, b) gs

--rules
-- rule1: equality
rule1 :: GlobalConstraint -> Event Element -> DecomposedConstraint -> Tree
rule1 gc e dc = let re = findReifiedEvent (removeFromDC e (getEventsFromDC dc)) in
    if re == None then Lit (findNonReifiedEvent (getEventsFromDC dc) (getEventSignature e), One) 
    else if getEventSignature e == getEventSignature re then makeTree re gc dc
         else makeTree (negateEvent re) gc dc 

-- rule2: comparison
rule2 :: GlobalConstraint -> Event Element -> DecomposedConstraint -> Tree
rule2 gc e dc = let re = findReifiedEvent (removeFromDC e (getEventsFromDC dc)) in
    if re == None then Lit (findNonReifiedEvent (getEventsFromDC dc) (getEventSignature e), One) 
    else if getEventSignature e == getEventSignature re then makeTree re gc dc
         else makeTree (negateEvent re) gc dc 

-- rule3: conjonction
rule3 :: GlobalConstraint -> Event Element -> DecomposedConstraint -> Tree
rule3 gc e dc = let re = findReifiedEvent (removeFromDC e (getEventsFromDC dc)) in
    let index = findAllIndex dc in
    if isMultipleInstances e dc then
        if getEventSignature e == getEventSignature re then AND (e, One, [makeTree re gc dc])
        else AND (e, One, makeTree (negateEvent re) gc dc : [multXOneMakeTree e index gc dc])
    else if getEventSignature e == getEventSignature re then multMakeTree re index gc dc
         else OR (e, All index, createExplanationTree gc (negateEvent re) dc)

-- rule4: disjonction
rule4 :: GlobalConstraint -> Event Element -> DecomposedConstraint -> Tree
rule4 gc e dc = let re = findReifiedEvent (removeFromDC e (getEventsFromDC dc)) in
    let index = findAllIndex dc in
    if re /= None then
        if isMultipleInstances e dc then
            if getEventSignature e == getEventSignature re then AND (e, One, makeTree re gc dc : [multXOneMakeTree (negateEvent e) index gc dc])
            else AND (e, One, [makeTree (negateEvent re) gc dc])
        else if getEventSignature e == getEventSignature re then OR (re, All index, createExplanationTree gc re dc)
            else multMakeTree (negateEvent re) index gc dc
    else
        if isMultipleInstances e dc then multXOneMakeTree (negateEvent e) index gc dc
        else Lit(None, One)

rule4bis :: GlobalConstraint -> Event Element -> DecomposedConstraint -> Tree
rule4bis gc e dc = let re = findReifiedEvent (removeFromDC e (getEventsFromDC dc)) in
    if re /= None then
        if getEventSignature e == getEventSignature re then OR (counterPropagate re, One, createExplanationTree (propagateGC gc re) (counterPropagate re) dc)
        else makeTree (negateEvent re) gc dc
    else
        if isMultipleInstances e dc then makeTree (negateEvent e) gc dc
        else Lit(None, One)

-- rule5: smaller than sum
rule5 :: GlobalConstraint -> Event Element -> DecomposedConstraint -> Tree
rule5 gc e dc = let re = findReifiedEvent (removeFromDC e (getEventsFromDC dc)) in
    let index = findAllIndex dc in
    if re /= None then
        if isMultipleInstances e dc then
            if getEventSignature e then
                if getEventSignature e == getEventSignature re then AND (e, One, makeTree (negateEvent re) gc dc : [multXOneMakeTree (negateEvent e) index gc dc])
                else AND (e, One, makeTree re gc dc : [multXOneMakeTree e index gc dc])
            else Lit (None, One)
        else
            if getEventSignature e == getEventSignature re then multMakeTree (negateEvent re) index gc dc
            else AND(e, All index, [multMakeTree re index gc dc])
    else
        if isMultipleInstances e dc && not(getEventSignature e) then multXOneMakeTree (negateEvent e) index gc dc
        else Lit (None, One)

-- rule6: bigger than sum
rule6 :: GlobalConstraint -> Event Element -> DecomposedConstraint -> Tree
rule6 gc e dc = let re = findReifiedEvent (removeFromDC e (getEventsFromDC dc)) in
    let index = findAllIndex dc in
    if re /= None then
        if isMultipleInstances e dc then
            if not(getEventSignature e) then
                if getEventSignature e == getEventSignature re then AND (e, One, makeTree re gc dc : [multXOneMakeTree e index gc dc])
                else AND (e, One, makeTree (negateEvent re) gc dc : [multXOneMakeTree (negateEvent e) index gc dc])
            else Lit (None, One)
        else
            if getEventSignature e == getEventSignature re then multMakeTree re index gc dc
            else multMakeTree (negateEvent re) index gc dc
    else
        if isMultipleInstances e dc && getEventSignature e then multXOneMakeTree e index gc dc
        else Lit (None, One)

-- rule7: equal to sum
rule7 :: GlobalConstraint -> Event Element -> DecomposedConstraint -> Tree
rule7 gc e dc = let re = findReifiedEvent (removeFromDC e (getEventsFromDC dc)) in
    let index = findAllIndex dc in
    if re /= None then
        if isMultipleInstances e dc then
            if not(getEventSignature e) then
                if getEventSignature e == getEventSignature re then AND (e, One, makeTree re gc dc : [multXOneMakeTree e index gc dc])
                else AND (e, One, makeTree (negateEvent re) gc dc : [multXOneMakeTree (negateEvent e) index gc dc])
            else
                if getEventSignature e == getEventSignature re then AND (e, One, makeTree (negateEvent re) gc dc : [multXOneMakeTree (negateEvent e) index gc dc])
                else AND (e, One, makeTree re gc dc : [multXOneMakeTree e index gc dc])
        else
            if getEventSignature e == getEventSignature re then multMakeTree re index gc dc
            else multMakeTree (negateEvent re) index gc dc
    else
        if isMultipleInstances e dc then
            if getEventSignature e then multXOneMakeTree (negateEvent e) index gc dc
            else multXOneMakeTree e index gc dc
        else Lit (None, One)

getRule :: DecomposedConstraint -> Integer
getRule (a, _, _) = a

applyRule :: GlobalConstraint -> Event Element -> DecomposedConstraint -> Tree
applyRule gc e dc | getRule dc == 1 = rule1 gc e dc
                  | getRule dc == 2 = rule2 gc e dc
                  | getRule dc == 2 = rule3 gc e dc
                  | getRule dc == 4 = rule4 gc e dc
                  | getRule dc == -4 = rule4bis gc e dc
                  | getRule dc == 5 = rule5 gc e dc
                  | getRule dc == 6 = rule6 gc e dc
                  | getRule dc == 7 = rule7 gc e dc

inverseVariationIndex :: Index -> Index
inverseVariationIndex i = Index {name = name i, variation = - variation i}

inverseVariationElement :: Element -> Element
inverseVariationElement (Var (e, i)) = Var (e, map inverseVariationIndex i)
inverseVariationElement (ReiVar (e, i)) = ReiVar (e, map inverseVariationIndex i)
inverseVariationElement (Ind i) = Ind (inverseVariationIndex i)
inverseVariationElement (Not e) = Not (inverseVariationElement e)
inverseVariationElement (Val v) = Val v

counterPropagateEvent :: Event Element -> Event Element
counterPropagateEvent (Equ (e1, e2)) = Equ (inverseVariationElement e1, inverseVariationElement e2)
counterPropagateEvent (Geq (e1, e2)) = Geq (inverseVariationElement e1, inverseVariationElement e2)
counterPropagateEvent (Leq (e1, e2)) = Leq (inverseVariationElement e1, inverseVariationElement e2)
counterPropagateEvent (And e) = And (map inverseVariationElement e)
counterPropagateEvent (Or e) = Or (map inverseVariationElement e)
counterPropagateEvent (Only e) = Only (inverseVariationElement e)
counterPropagateEvent None = None

counterPropagate :: Event Element -> Event Element
counterPropagate e | getEventSignature e = e 
                    |otherwise = counterPropagateEvent e

variationIndex :: Index -> Bool -> Index -> Index
variationIndex i1 b i2 | name i1 == name i2 && b = Index{name= name i1, variation = variation i2 + variation i1}
                       | name i1 == name i2 && not b = Index{name= name i1, variation = variation i2 - variation i1}
                       | otherwise = i2

variationIndexElement :: Index -> Bool -> Element -> Element
variationIndexElement i b (Var (v, ix)) = Var (v, map (variationIndex i b) ix)
variationIndexElement i b (ReiVar (v, ix)) = ReiVar (v, map (variationIndex i b) ix)
variationIndexElement i b (Ind ix) = Ind (variationIndex i b ix)
variationIndexElement i b (Not e) = variationIndexElement i b e 
variationIndexElement i _ (Val v) = Val v

variationIndexEvent :: Index -> Bool -> Event Element -> Event Element
variationIndexEvent i b (Equ (e1, e2)) = Equ (variationIndexElement i b e1, variationIndexElement i b e2)
variationIndexEvent i b (Geq (e1, e2)) = Geq (variationIndexElement i b e1, variationIndexElement i b e2)
variationIndexEvent i b (Leq (e1, e2)) = Leq (variationIndexElement i b e1, variationIndexElement i b e2)
variationIndexEvent i b (And e) = And (map (variationIndexElement i b) e)
variationIndexEvent i b (Or e) = Or (map (variationIndexElement i b) e)
variationIndexEvent i b (Only e) = Only (variationIndexElement i b e)
variationIndexEvent _ _ None = None

propagateIndex :: DecomposedConstraint -> Bool -> [Index] -> DecomposedConstraint
propagateIndex (r, s, e) b (i:is) = propagateIndex (r, s, map (variationIndexEvent i b) e) b is 
propagateIndex d _ [] = d 

propagateDC :: Event Element -> DecomposedConstraint -> DecomposedConstraint
propagateDC e d = let indexE = getEventIndices (getElements e) in propagateIndex d (getEventSignature e) indexE

propagateGC :: GlobalConstraint -> Event Element -> GlobalConstraint
propagateGC g e = map (propagateDC e) g 
    
--TODO: clean-up all that (probable repetition)
makeTree :: Event Element -> GlobalConstraint -> DecomposedConstraint -> Tree
makeTree None _ _ = Lit (None, One)
makeTree e gc previousdc = AND (counterPropagate e, One, createExplanationTree (propagateGC gc e) (counterPropagate e) previousdc)

multXOneMakeTree :: Event Element -> Index -> GlobalConstraint -> DecomposedConstraint -> Tree
multXOneMakeTree None _ _ _ = Lit (None, One)
multXOneMakeTree e i gc previousdc = AND (e, AllButOne i, createExplanationTree gc e previousdc)

multMakeTree :: Event Element -> Index -> GlobalConstraint -> DecomposedConstraint -> Tree
multMakeTree None _ _ _ = Lit (None, One)
multMakeTree e i gc previousdc = AND (e, All i, createExplanationTree gc e previousdc)

-- we want to call the explanation rules and use them to create the explanation tree (look at rule[0-7] and find)
createExplanationTree :: GlobalConstraint -> Event Element -> DecomposedConstraint -> [Tree]
createExplanationTree gc e previousdc = map (applyRule gc e) (findEventInGC (removeDCFromGC previousdc gc) e)

-- TODO: finish
concatTree :: [[Event Element]] -> [Event Element]
concatTree = concat 

{-solveExplanationTree :: Tree -> String
solveExplanationTree (Lit (x, _)) = x
solveExplanationTree (OR (_, _, t)) = concatMap solveExplanationTree t
solveExplanationTree (AND (_, _, t)) = concatTree (map solveExplanationTree t)
-}

explain :: GlobalConstraint -> Event Element -> Tree
explain g e = OR (e, One, createExplanationTree g e emptyDecomposedConstraint)

--examples
emptyDecomposedConstraint :: DecomposedConstraint
emptyDecomposedConstraint = (0, [], [])

indexI0 :: Index
indexI0 = Index {name="i", variation=0}
indexT0 :: Index
indexT0 = Index {name="t", variation=0}
indexJ0 :: Index
indexJ0 = Index {name="j", variation=0}

allDiff :: GlobalConstraint
allDiff = [(1, [Each indexI0, Each indexT0], [Equ (Var ("X", [indexI0]), Ind indexT0), Only (ReiVar ("b1", [indexI0, indexT0]))]),
           (5, [All indexI0, Each indexT0], [Leq (ReiVar ("b1", [indexI0, indexT0]), Val 1)])]

increasing :: GlobalConstraint
increasing = [(2, [Each indexI0, Each indexT0], [Geq (Var ("X", [indexI0]), Ind indexT0), Only (ReiVar ("b1", [indexI0, indexT0]))]),
              (-4, [Each indexI0, Each indexT0], [Or [Not (ReiVar ("b1", [Index {name="i", variation= -1}, indexT0])), ReiVar ("b1", [indexI0, indexT0])]])]

knapsackSimplified :: GlobalConstraint
knapsackSimplified = [(1, [Each indexI0], [Equ (Var ("X", [indexI0]), Val 1), Only (ReiVar ("b1", [indexI0]))]),
                      (7, [All indexI0], [Equ (ReiVar ("b1", [indexI0]), Var ("P", []))]),
                      (7, [All indexI0], [Equ (ReiVar ("b1", [indexI0]), Var ("W", []))])]

knapsack :: GlobalConstraint
knapsack = [(1, [Each indexI0, Each indexJ0], [Equ (Var ("X", [indexI0]), Ind indexJ0), Only (ReiVar ("b1", [indexI0, indexJ0]))]),
            (7, [All indexI0, All indexJ0], [Equ (ReiVar ("b1", [indexI0, indexJ0]), Var ("P", []))]),
            (7, [All indexI0, All indexJ0], [Equ (ReiVar ("b1", [indexI0, indexJ0]), Var ("W", []))])]

testDC :: DecomposedConstraint
testDC = (2, [Each indexI0, Each indexT0], [Geq (Var ("X", [indexI0]), Ind indexT0), Only (ReiVar ("b1", [indexI0, indexT0]))])

testDC2 :: DecomposedConstraint
testDC2 = (-4, [Each indexI0, Each indexT0], [Or [Not (ReiVar ("b1", [Index {name="i", variation= -1}, indexT0])), ReiVar ("b1", [indexI0, indexT0])]])

testEvent :: Event Element
testEvent = Only (ReiVar ("b1", [Index {name="i", variation= -1}, indexT0]))

testEvent2 :: Event Element
testEvent2 = Only (ReiVar ("b1", [indexI0, indexT0]))

testEvent3 :: Event Element
testEvent3 = Only(ReiVar ("b1", [Index {name="i", variation= 1}, indexT0]))

eventEx :: Event Element
eventEx = Equ (Not (Var ("X", [indexI0])), Ind indexT0)

eventEx2 :: Event Element
eventEx2 = Equ(Var ("X", [indexI0]), Val 1)

eventEx3 :: Event Element
eventEx3 = Equ(Var ("X", [indexI0]), Ind indexJ0)

eventEx4 :: Event Element
eventEx4 = Geq(Not (Var ("X", [indexI0])), Ind indexT0)

-- tests
test1 :: [DecomposedConstraint]
test1 = findEventInGC allDiff eventEx

test2 :: Event Element
test2 = findReifiedEvent (getEventsFromDC (head test1))

test3 :: Tree
test3 = OR (eventEx, One, createExplanationTree allDiff eventEx emptyDecomposedConstraint)

test4 :: Event Element
test4 = findReifiedEvent (delete eventEx (getEventsFromDC (head test1)))

{-test5 :: [Event Element]
test5 = solveExplanationTree test3
-}
test6 :: [Event Element]
test6 = removeFromDC (Only (ReiVar ("b1", [Index {name="i", variation=0}, Index {name="t", variation=0}]))) (getEventsFromDC (5, [All Index {name="i", variation=0}, Each Index {name="t", variation=0}], [Leq (ReiVar ("b1", [Index {name="i", variation=0}, Index {name="t", variation=0}]), Val 1)]))

test7 :: [Tree]
test7 = createExplanationTree allDiff eventEx emptyDecomposedConstraint

test7bis :: Tree
test7bis = OR (eventEx, One, test7)
-- OR (Equ (Var ("X",["i"]),Ind "t"),One,[AND (Only (ReiVar ("b1",["i","t"])),One,[AND (Only (ReiVar ("b1",["i","t"])),One,[Lit (None,One),AND (Only (Not (ReiVar ("b1",["i","t"]))),AllButOne "i",[Lit (Equ (Not (Var ("X",["i"])),Ind "t"),One)])])])])

test8 :: Tree
test8 = OR (eventEx2, One, createExplanationTree knapsackSimplified eventEx2 emptyDecomposedConstraint)

test9 :: [Tree]
test9 = createExplanationTree knapsack eventEx3 emptyDecomposedConstraint

test9bis :: Tree
test9bis = OR (eventEx3, One, test9)

test10 :: Tree
test10 = OR (eventEx4, One, createExplanationTree increasing eventEx4 emptyDecomposedConstraint)