import Data.Text.Internal.Builder.Functions (i2d)
import Data.Fixed (E2)
import Data.List
import Language.Haskell.TH (match)
import Distribution.Simple.LocalBuildInfo (withAllComponentsInBuildOrder)
import Distribution.Simple.Command (OptDescr(BoolOpt))

-- type definitions
type Index = String
data Scope = All Index | Each Index deriving Show
instance Eq Scope where
    All i1 == All i2 = i1==i2
    Each i1 == Each i2 = i1==i2
    _ == _ = False
data Element = Var (String, [Index]) | ReiVar (String, [Index]) | Ind Index | Not Element deriving Show
instance Eq Element where
    Var (s1, i1) == Var (s2, i2) = s1==s2 && i1==i2
    ReiVar (s1, i1) == ReiVar (s2, i2) = s1==s2 && i1==i2
    Ind i1 == Ind i2 = i1==i2
    Not e1 == Not e2 = e1==e2
    _ == _ = False
-- not sure Or and And are useful
data Event a = Equ (a, a) | Leq (a, a) | Geq (a, a) | Or [a] | And [a] | Only a | None deriving Show
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

data Tree = Lit (Event Element) | EXOR (Event Element, [Tree]) | EXAND (Event Element, [Tree]) deriving Show

-- research functions
getElementSignature :: Element -> Bool 
getElementSignature (Not _) = False 
getElementSignature _ = True

getEventSignature :: Event Element -> Bool 
getEventSignature (Equ (e1, e2)) = getElementSignature e1 == getElementSignature e2
getEventSignature (Leq (e1, e2)) = getElementSignature e1 == getElementSignature e2
getEventSignature (Geq (e1, e2)) = getElementSignature e1 == getElementSignature e2
getEventSignature (Or e) = undefined
getEventSignature (And e) = undefined
getEventSignature (Only e) = getElementSignature e
getEventSignature None = True

getElementName :: Element -> String
getElementName (Var (s, _)) = s 
getElementName (ReiVar (s, _)) = s 
getElementName (Ind s) = s 
getElementName (Not e) = getElementName e

negateElement :: Element -> Element
negateElement = Not

getScopeAllIndices :: [Scope] -> [Index]
getScopeAllIndices ((All i):sl) = i : getScopeAllIndices sl
getScopeAllIndices ((Each i): sl) = getScopeAllIndices sl
getScopeAllIndices [] = [] 

getElementIndices :: Element -> [Index]
getElementIndices (Var (_, i)) = i 
getElementIndices (ReiVar (_, i)) = i 
getElementIndices (Ind i) = [i]
getElementIndices (Not e) = getElementIndices e 

getEventIndices :: Event Element -> [Index]
getEventIndices (Equ (e1, e2)) = getElementIndices e1 ++ getElementIndices e2
getEventIndices (Leq (e1, e2)) = getElementIndices e1 ++ getElementIndices e2
getEventIndices (Geq (e1, e2)) = getElementIndices e1 ++ getElementIndices e2
getEventIndices (Or e) = concat (map getElementIndices e) 
getEventIndices (And e) = concat (map getElementIndices e)
getEventIndices (Only e) = getElementIndices e
getEventIndices None = []

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

isInList :: Eq a => [a] -> a -> Bool 
isInList (l:ls) e | l==e = True
                  | otherwise = isInList ls e
isInList [] e = False

findEventInGC :: GlobalConstraint -> Event Element -> [DecomposedConstraint]
findEventInGC (c:cs) e | isInList (getEventsFromDC c) e = c : findEventInGC cs e
                       | otherwise = findEventInGC cs e
findEventInGC [] e = []

isReified :: Element -> Bool
isReified (ReiVar r) = True
isReified _ = False

findReifiedEvent :: [Event Element] -> Event Element
findReifiedEvent ((Equ (e1, e2)):ls) | isReified e1 = Equ (e1, e2)
                                       | isReified e2 = Equ (e1, e2) 
                                       | otherwise = findReifiedEvent ls 
findReifiedEvent ((Leq (e1, e2)):ls) | isReified e1 = Leq (e1, e2) 
                                       | isReified e2 = Leq (e1, e2) 
                                       | otherwise = findReifiedEvent ls
findReifiedEvent ((Geq (e1, e2)):ls) | isReified e1 = Geq (e1, e2) 
                                       | isReified e2 = Geq (e1, e2) 
                                       | otherwise = findReifiedEvent ls                                      
findReifiedEvent ((Or e):ls) = undefined 
findReifiedEvent ((And e):ls) = undefined
findReifiedEvent ((Only e):ls) | isReified e = Only e
                               | otherwise = findReifiedEvent ls 
findReifiedEvent [] = None

isMultipleInstances :: Event Element -> DecomposedConstraint -> Bool
isMultipleInstances e (_, s, _) = let i = getEventIndices e in
    let si = getScopeAllIndices s in
    search i si
    where search :: [String] -> [String] -> Bool
          search (i:is) si | elem i si = True 
                         | otherwise = search is si 
          search [] _ = False

propagate :: Event Element -> Event Element
propagate e = e

--rules
-- rule1: equality
rule1 :: GlobalConstraint -> Event Element -> DecomposedConstraint -> Tree
rule1 gc e dc = let re = findReifiedEvent (delete e (getEventsFromDC dc)) in
    if re == None then Lit e
    else if getEventSignature e == getEventSignature re then makeTree re gc dc
         else makeTree (negateEvent re) gc dc 

-- rule2: comparison
rule2 :: GlobalConstraint -> Event Element -> DecomposedConstraint -> Tree
rule2 gc e dc = let re = findReifiedEvent (delete e (getEventsFromDC dc)) in
    if re == None then Lit e
    else if getEventSignature e == getEventSignature re then makeTree re gc dc
         else makeTree (negateEvent re) gc dc 

-- rule3: conjonction
rule3 :: GlobalConstraint -> Event Element -> DecomposedConstraint -> Tree
rule3 gc e dc = let re = findReifiedEvent (delete e (getEventsFromDC dc)) in
    if isMultipleInstances e dc then
        if getEventSignature e == getEventSignature re then EXAND (e, [makeTree re gc dc])
        else EXAND (e, makeTree (negateEvent re) gc dc : multXOneMakeTree e gc dc)
    else if getEventSignature e == getEventSignature re then EXAND (e, multMakeTree re gc dc)
         else EXOR (e, multMakeTree (negateEvent re) gc dc)

-- rule4: disjonction
rule4 :: GlobalConstraint -> Event Element -> DecomposedConstraint -> Tree
rule4 gc e dc = let re = findReifiedEvent (delete e (getEventsFromDC dc)) in
    if isMultipleInstances e dc then
        if getEventSignature e == getEventSignature re then EXAND (e, makeTree re gc dc : multXOneMakeTree (negateEvent e) gc dc)
        else EXAND (e, [makeTree (negateEvent re) gc dc])
    else if getEventSignature e == getEventSignature re then EXOR (e, multMakeTree re gc dc)
         else EXAND (e, multMakeTree (negateEvent re) gc dc)

-- rule5: smaller than sum
rule5 :: GlobalConstraint -> Event Element -> DecomposedConstraint -> Tree
rule5 gc e dc = let re = findReifiedEvent (delete e (getEventsFromDC dc)) in
    if isMultipleInstances e dc then
        if getEventSignature e == getEventSignature re then EXAND (e, makeTree (negateEvent re) gc dc : multXOneMakeTree (negateEvent e) gc dc)
        else EXAND (e, makeTree re gc dc : multXOneMakeTree e gc dc)
    else
        if getEventSignature e == getEventSignature re then EXAND(e, multMakeTree (negateEvent re) gc dc)
        else EXAND(e, multMakeTree re gc dc)

-- rule6: bigger than sum
rule6 :: GlobalConstraint -> Event Element -> DecomposedConstraint -> Tree
rule6 gc e dc = let re = findReifiedEvent (delete e (getEventsFromDC dc)) in
    if isMultipleInstances e dc then
        if getEventSignature e == getEventSignature re then EXAND (e, makeTree re gc dc : multXOneMakeTree e gc dc)
        else EXAND (e, makeTree (negateEvent re) gc dc : multXOneMakeTree (negateEvent e) gc dc)
    else
        if getEventSignature e == getEventSignature re then EXAND(e, multMakeTree re gc dc)
        else EXAND(e, multMakeTree (negateEvent re) gc dc)

-- rule7: equal to sum
rule7 :: GlobalConstraint -> Event Element -> DecomposedConstraint -> Tree
rule7 gc e dc = makeTree (findReifiedEvent (delete e (getEventsFromDC dc))) gc dc

getRule :: DecomposedConstraint -> Integer
getRule (a, _, _) = a

removeConstraint :: DecomposedConstraint -> GlobalConstraint -> GlobalConstraint
removeConstraint = undefined

applyRule :: GlobalConstraint -> Event Element -> DecomposedConstraint -> Tree
applyRule gc e dc | getRule dc == 1 = rule1 gc e dc
                  | getRule dc == 2 = rule2 gc e dc
                  | getRule dc == 2 = rule3 gc e dc
                  | getRule dc == 4 = rule4 gc e dc
                  | getRule dc == 5 = rule5 gc e dc
                  | getRule dc == 6 = rule6 gc e dc
                  | getRule dc == 7 = rule7 gc e dc

makeTree :: Event Element -> GlobalConstraint -> DecomposedConstraint -> Tree
makeTree e gc previousdc = EXAND (e, createExplanationTree gc (propagate e) previousdc)

multXOneMakeTree :: Event Element -> GlobalConstraint -> DecomposedConstraint -> [Tree]
multXOneMakeTree = undefined

multMakeTree :: Event Element -> GlobalConstraint -> DecomposedConstraint -> [Tree]
multMakeTree = undefined

-- we want to call the explanation rules and use them to create the explanation tree (look at rule[0-7] and find)
createExplanationTree :: GlobalConstraint -> Event Element -> DecomposedConstraint -> [Tree]
createExplanationTree gc e previousdc = map (applyRule gc e) (findEventInGC (delete previousdc gc) e)

-- TODO: finish
concatTree :: [[Event Element]] -> [Event Element]
concatTree = concat 

solveExplanationTree :: Tree -> [Event Element]
solveExplanationTree (Lit x) = [x]
solveExplanationTree (EXOR (c, t)) = concatMap solveExplanationTree t
solveExplanationTree (EXAND (c, t)) = concatTree (map solveExplanationTree t)

explain :: GlobalConstraint -> Event Element -> [Event Element]
explain g e = solveExplanationTree (EXOR (e, createExplanationTree g e emptyDecomposedConstraint))

--examples
emptyDecomposedConstraint :: DecomposedConstraint
emptyDecomposedConstraint = (0, [], [])

allDiff :: GlobalConstraint
allDiff = [(1, [Each "i", Each "t"], [Equ (Var ("X", ["i"]), Ind "t"), Only (ReiVar ("b1", ["i", "t"]))]),
           (5, [All "i", Each "t"], [Only (ReiVar ("b1", ["i", "t"]))])]

eventEx :: Event Element
eventEx = Equ (Var ("X", ["i"]), Ind "t")

-- tests
test1 :: [DecomposedConstraint]
test1 = findEventInGC allDiff eventEx

test2 :: Event Element
test2 = findReifiedEvent (getEventsFromDC (head test1))

test3 :: Tree
test3 = EXOR (eventEx, createExplanationTree allDiff eventEx emptyDecomposedConstraint)

test4 :: Event Element
test4 = findReifiedEvent (delete eventEx (getEventsFromDC (head test1)))

test5 :: [Event Element]
test5 = solveExplanationTree test3