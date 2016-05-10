import Prelude hiding (sum,foldr,concatMap,concat)
import System.Environment
import Data.List(transpose,groupBy)
import Data.Foldable
import Control.Applicative

import Control.Monad

class Vector v where
  (<->) :: Num a => v a -> v a -> v a
  (<+>) :: Num a => v a -> v a -> v a
  (<.>) :: Num a =>  a-> v a -> v a
  dist2 :: (Num a,Floating a) => v a -> v a -> a
  zero ::  Num a => Int -> v a
  quad1 ::  (Fractional a, Ord a, Num a) => v a -> a -> v a -> v a

instance Vector [] where
  (<->) x y = zipWith (-) (x) (y)
  (<+>) x y = zipWith (+) (x) (y)
  (<.>) x y = map (*x) y
  dist2 v v' = sqrt.sum.map (**2) $  v <-> v'
  zero x = concat $ replicate x [0] 
  quad1 (a:ab:ae:_) b (x:y:z:_) 
   | x>=a && y>=ab && z >=ae = [(a+b/2),(ab+b/2),(ae+b/2)]
   | x<=a && y>=ab && z >=ae= [(a-b/2),(ab+b/2),(ae+b/2)]
   | x>=a && y<=ab && z >=ae= [(a+b/2),(ab-b/2),(ae+b/2)]
   | x<=a && y<=ab && z >=ae= [(a-b/2),(ab+b/2),(ae+b/2)]
   | x>=a && y>=ab && z <=ae= [(a+b/2),(ab+b/2),(ae-b/2)]
   | x<=a && y>=ab && z <=ae= [(a-b/2),(ab+b/2),(ae-b/2)]
   | x>=a && y<=ab && z <=ae= [(a+b/2),(ab-b/2),(ae-b/2)]
   | x<=a && y<=ab && z <=ae= [(a-b/2),(ab+b/2),(ae-b/2)]   

data Vec a =  Vec [a] | InvalidVec deriving(Show,Eq)

instance Vector Vec where
   (<+>) InvalidVec InvalidVec = InvalidVec
   (<+>) _ InvalidVec = InvalidVec
   (<+>) InvalidVec _ = InvalidVec
   (<+>) (Vec x) (Vec y) = if (length x) == (length y) then (Vec (x <+> y)) else InvalidVec
   (<->) InvalidVec InvalidVec = InvalidVec
   (<->) _ InvalidVec = InvalidVec
   (<->) InvalidVec _ = InvalidVec
   (<->) (Vec x) (Vec y) = if (length x) == (length y) then (Vec (x <-> y)) else InvalidVec
   (<.>) _ InvalidVec = InvalidVec
   (<.>) x (Vec y) = (Vec (x <.> y))
   dist2 (Vec x) (Vec y) = dist2 x y
   zero x = Vec (concat $ replicate x [0]) 
   quad1 (Vec l1) b (Vec l2) = Vec (quad1 l1 b l2)
   
instance Functor Vec where
  fmap f InvalidVec = InvalidVec
  fmap f (Vec a) = Vec (map f a)

instance Applicative Vec where
   pure x = Vec (pure x)
   InvalidVec <*> InvalidVec = InvalidVec
   InvalidVec <*> _ = InvalidVec
   _ <*> InvalidVec = InvalidVec
   (Vec fs) <*> (Vec xs)  = Vec (zipWith ($) fs xs)

instance Monad Vec where
  return x = Vec (return x) 
  InvalidVec >>= f = InvalidVec
  Vec ([]) >>= f = Vec []
  Vec (a:b)  >>= f = Vec ((getelem (f a)) ++ (getelem ((Vec b) >>= f )) ) 


getelem :: (Vec a)-> [a]
getelem (Vec x) = x

main :: IO ()
main = do
  args <- getArgs
  contents <- getContents
  putStr.unlines.applyBH args $ lines contents

applyBH :: [String] -> [String] -> [String]
applyBH (tm:dt:[]) (cnt:r:bodies) =
  let bodiesIn = map (readBody.words) $ take (read cnt) bodies
      bodiesOut = barnesHut (read tm) (read dt) (read r) bodiesIn in
  cnt:r:(map show1 bodiesOut)
applyBH _ _ = error "Invalid input"

show1 :: Body Vec -> String
show1 (Body x y z) = show x ++ show y ++ show z

data Body v  = Body (v Double)  (v Double) Double 

readBody :: [String] -> Body Vec
readBody (x:y:z:vx:vy:vz:m:_) = Body (Vec [read x,read y,read z]) (Vec [read vx,read vy,read vz]) (read m)
readBody _ = error "Invalid input"

barnesHut :: Double -> Double -> Double -> [Body Vec ] -> [Body Vec]
barnesHut tm dt r bodies = snd $ (until ((<=0).fst) (tick dt r)) (tm, bodies)

tick :: Double -> Double -> (Double, [Body Vec]) -> (Double, [Body Vec])
tick dt r (tm, bodies) =
  let tree = makeQT (zero 3) r pos summary bodies in
  (tm-dt, map (updateBody tree dt) bodies) 
updateBody :: (FoldableTree (Body Vec)) -> Double -> Body Vec -> Body Vec
updateBody tree dt (Body p v m) =
  let threshold = 0.5
      sumOk r (Body c _ _) = r/(dist2 p c) < threshold
      (Body a b c) = (visitQT' sumOk (calcAcc' p ) tree)
      v' =  v  <+> Vec (dt <.> get' b)
      p' =  p  <+> (dt <.> v') in
  Body p' v' m

pos :: Body Vec -> Vec Double
pos (Body p _ _) = p

pos' :: Body Vec -> [Double]
pos' b = get' (pos b)

summary :: [Body Vec] -> Body Vec
summary bodies =
  let masses = map (\(Body _ _ m)->m) bodies
      totalM = sum masses
      wPos = transpose $ zipWith (\m->map (m*)) masses $  map pos' bodies in
  Body (Vec (map ((/totalM).sum) wPos)) (Vec (zero 3)) totalM


dist :: [Double] -> [Double] -> Double
dist v v' = sqrt.sum.map (**2) $  v <-> v'

calcAcc' :: Vec Double -> Body Vec -> Body Vec -> Body Vec
calcAcc' p (Body p' _ m') (Body p'' _ m'') =
  let constG = 0.0000000000667
      f1 = constG * m'' / (dist2 p p' ** 3) 
      f2 = constG * m' / (dist2 p p'' ** 3)
      a1 = if p /= p'  then  ( f1 <.> (p'<-> p)) else zero 3
      a2 = if p /= p''   then  (f2 <.> (p''<-> p)) else zero 3 in
     Body (Vec (zero 3))  (a1<+>a2) 0  

calcAcc :: Vec Double -> Body Vec -> Vec Double
calcAcc p (Body p' _ m') =
  let constG = 0.0000000000667
      accel = constG * m' / (dist2 p p' ** 3) in
  if p==p' then  (zero 3) else  ( accel <.> (p'<-> p) )

data QT a = QT Double a [QT a]

get' :: Vec Double -> [Double]
get' (Vec d) = d

makeQT :: Vec Double -> Double -> (Body Vec->Vec Double) -> ([Body Vec]->Body Vec) -> [Body Vec] -> (FoldableTree (Body Vec))
makeQT _ _ _ _ [] = error "No data to make tree"
makeQT _ r _ _ [x] = FoldableTree (\x y -> True) r x []
makeQT c r toXY f nodes =
  let quad b = map (\x->if x then r/2 else -r/2) $ zipWith (<) (get' c) (get' (toXY b))
      quads = groupBy (\a b->quad a==(quad b)) nodes in
  FoldableTree (\x y -> True)  r (f nodes) $ map (\n->makeQT (quad1 c r (toXY (head n))) (r/2) toXY f n) quads

visitQT :: (Double->(Body Vec)->Bool) -> ((Body Vec)->(Vec Double)) -> (QT (Body Vec)) -> [(Vec Double)]
visitQT _ dF (QT _ d []) = [dF d]
visitQT sF dF (QT r s children) =
  if sF r s then [dF s] else concatMap (visitQT sF dF) children


visitQT' :: (Double->(Body Vec)->Bool) ->((Body Vec)->(Body Vec)->(Body Vec)) -> (FoldableTree (Body Vec)) -> Body Vec
visitQT' sF dF (FoldableTree a b c d ) = foldr dF (Body (zero 3) (zero 3) 0 )  (FoldableTree sF b c d)  


data FoldableTree a = FoldableTree (Double->(a)->Bool) Double a [FoldableTree a]

instance  Foldable (FoldableTree ) where
   foldr calcacc z (FoldableTree sumok y x []) = calcacc x z
   foldr calcacc z (FoldableTree sumok  y x l)
    | sumok y x = calcacc x z
   foldr calcacc z (FoldableTree sumok  y x (q1:[])) = calcacc x (foldr calcacc z (q1))
   foldr calcacc z (FoldableTree sumok  y x (q1:q2:[])) =  calcacc x (foldr calcacc (foldr calcacc z (q1)) (q2)) 
   foldr calcacc z (FoldableTree sumok  y x (q1:q2:q3:[])) = calcacc x (foldr calcacc (foldr calcacc ((foldr calcacc z (q1))) (q2)) (q3))
   foldr calcacc z (FoldableTree sumok  y x (q1:q2:q3:q4:[])) =  calcacc x (foldr calcacc (foldr calcacc (foldr calcacc ((foldr calcacc z (q4))) (q3)) (q2)) q1)
   foldr calcacc z (FoldableTree sumok  y x (q1:q2:q3:q4:q5:[])) =   calcacc x (foldr calcacc (foldr calcacc (foldr calcacc (foldr calcacc ((foldr calcacc z (q4))) (q3)) (q2)) q1) q5) 
   foldr calcacc z (FoldableTree sumok  y x (q1:q2:q3:q4:q5:q6:[])) = calcacc x(foldr calcacc (foldr calcacc (foldr calcacc (foldr calcacc (foldr calcacc ((foldr calcacc z (q4))) (q3)) (q2)) q1) q5) q6)  
   foldr calcacc z (FoldableTree sumok  y x (q1:q2:q3:q4:q5:q6:q7:[])) =  calcacc x (foldr calcacc (foldr calcacc (foldr calcacc (foldr calcacc (foldr calcacc (foldr calcacc ((foldr calcacc z (q4))) (q3)) (q2)) q1) q5) q6) q7)
   foldr calcacc z (FoldableTree sumok  y x (q1:q2:q3:q4:q5:q6:q7:q8:_)) = calcacc x (foldr calcacc (foldr calcacc (foldr calcacc (foldr calcacc (foldr calcacc (foldr calcacc (foldr calcacc ((foldr calcacc z (q4))) (q3)) (q2)) q1) q5) q6) q7) q8)
