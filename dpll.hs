-- Nom et prénom: VU Nguyen Phuong Vy
-- L2 Informatique Groupe 2A
-- Nombre d'étudiant: 21911658

type Var = Char

data Litteral = Pos Var | Neg Var
    deriving (Show, Eq)

type Clause = [Litteral] -- liste de positif ou negatif
type Formule = [Clause] 
type Distribution = [(Var, Bool)]

f1 = [[Pos 'a', Pos 'b'], [Neg 'a', Neg 'b'], [Pos 'a', Neg 'b']]

f2 = [[Pos 'a', Pos 'c', Neg 'b'], [Pos 'a', Neg 'c'], [Neg 'a', Pos 'b', Neg 'c'], [Neg 'a', Neg 'b']]

f3 = [[Pos 'a', Pos 'b'], [Pos 'a', Neg 'b'],[Neg 'a', Pos 'b'],[Neg 'a', Neg 'b']]

f4 = [[Pos 'a', Pos 'c', Neg 'b'], [Pos 'a', Neg 'c', Pos 'b'], [Neg 'a', Pos 'b', Neg 'c'], [Neg 'a', Neg 'b']] 
f5 = [[Pos 'a', Pos 'b'], [Pos 'a', Neg 'b'], [Neg 'a', Pos 'b'], [Neg 'a', Neg 'b']] 

f6 = [[Pos 'a', Neg 'a'], [Pos 'c'], [Neg 'a', Pos 'b', Neg 'c'], [Pos 'a', Neg 'b'], [Pos 'a', Pos 'c'], [Pos 'a', Pos 'b', Neg 'c']]


-- 1. Methode de type 'Generate and Test'

listeVarsClause :: Clause -> [Var] 
listeVarsClause [] = []
listeVarsClause ((Pos x):xs) = x : listeVarsClause xs
listeVarsClause ((Neg x):xs) = x : listeVarsClause xs

listeVarsFormule :: Formule -> [Var]
listeVarsFormule [] = []
listeVarsFormule (x:xs) = listeVarsClause x ++ listeVarsFormule xs


rmdups :: Eq a => [a] -> [a]
rmdups [] = []
rmdups (x:ys)
    | x `elem` ys = rmdups ys
    | otherwise = x : rmdups ys


listeVars :: Formule -> [Var]
listeVars cs = rmdups (listeVarsFormule cs)


-- 1.2

val :: Var -> Distribution -> Bool 
val x ((y, v):ys)
    | x == y = v
    | otherwise = val x ys


valeur :: Litteral -> Distribution -> Bool
valeur (Pos x) dist = val x dist
valeur (Neg x) dist = not (val x dist)


evalue :: Formule -> Distribution -> Bool
evalue formule dist = and [ or [valeur lit dist | lit <- clause] | clause <- formule]



-- 1.3
genereTable :: [Var] -> [Distribution]
genereTable [] = [[]]
genereTable (x:xs) = map ((x, True):) (genereTable xs) ++ map ((x, False):) (genereTable xs)


-- 1.4
sontSatis :: Formule -> [Distribution]
sontSatis f = filter (evalue f) (genereTable (listeVars f))


-- 1.5
nbDistri :: Formule -> Int
nbDistri f = length (sontSatis f)

-- grandeur rapporter 2^n (ou n est le nombre de variable de f)
ratio :: Formule -> Float
ratio f = fromIntegral (nbDistri f) / fromIntegral (2 ^ length (listeVars f))



-- 2. Prétraitement : Suppression des tautologies

negation :: Litteral -> Litteral
negation (Pos a) = Neg a
negation (Neg a) = Pos a 


estTauto :: Clause -> Bool
estTauto ls = and [ or [ valeur lit dist | lit <- ls ] | dist <- genereTable (rmdups (listeVarsClause ls))]


elimineTauto :: Formule -> Formule
elimineTauto = filter (not . estTauto)
 

-- 3.1 Existence d’une distribution : mise en œuvre de DPLL(v1)

estUnitaire :: Clause -> Bool
estUnitaire c 
    | length c == 1 = True
    | otherwise = False

estEvidtContradic :: Formule -> Bool 
estEvidtContradic [] = False
estEvidtContradic cs = chercher (clause cs)
    where chercher [] = False
          chercher (c:cs)
             | negation c `elem` cs = True 
             | otherwise = chercher cs
          clause [] = []
          clause (c:cs) 
             | estUnitaire c = c ++ clause cs 
             | otherwise = clause cs 


-- 3.2 Simplification : règle du littéral seul (ou règle de la clause unitaire)

existeSeul :: Formule -> Bool
existeSeul [] = False 
existeSeul (c:cs)
    | estUnitaire c = True 
    | otherwise = existeSeul cs 


trouveSeul :: Formule -> Litteral
trouveSeul [] = error "Pas trouvé"
trouveSeul (c:cs)
    | estUnitaire c = head c
    | otherwise = trouveSeul cs


elimineSeul :: Formule -> Litteral -> Formule
elimineSeul [] _ = []
elimineSeul (c:cs) lit
    | lit `elem` c = elimineSeul cs lit
    | negation lit `elem` c = elimineLit c (negation lit) : elimineSeul cs lit
    | otherwise = c : elimineSeul cs lit
        where elimineLit [] _ = []
              elimineLit (c:cs) lit 
                | c == lit = elimineLit cs lit 
                | otherwise = c : elimineLit cs lit 


-- 3.3 Simplification : règle du littéral pur

existePur :: Formule -> Bool 
existePur cs = existe (rmdups (concat cs))
    where existe [] = False
          existe (c:cs) 
            | negation c `notElem` cs = True 
            | otherwise = existe (filter (/= negation c) cs)


trouvePur :: Formule -> Litteral
trouvePur [] = error "Pas trouvé"
trouvePur cs = head (supprimer (rmdups (concat cs)))
    where supprimer [] = []
          supprimer (c:cs)
            | negation c `notElem` cs = c : supprimer cs
            | otherwise = supprimer (filter (/= negation c) cs)


eliminePur :: Formule -> Litteral -> Formule 
eliminePur [] _ = []
eliminePur (c:cs) lit
    | lit `elem` c = eliminePur cs lit
    | otherwise = c : eliminePur cs lit


-- 3.4 Recherche exhaustive (splitting)

dpll :: Formule -> Bool 
dpll = estSatis . elimineTauto

estSatis :: Formule -> Bool 
estSatis [] = True 
estSatis f 
    | estEvidtContradic f = False
    | existeSeul f = estSatis (elimineSeul f (trouveSeul f))
    | existePur f = estSatis (eliminePur f (trouvePur f))
    | otherwise = estSatis (elimineSeul f (head (concat f))) || estSatis (elimineSeul f (negation (head (concat f)))) 

