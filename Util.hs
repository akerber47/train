module Util
( untilFixed
, untilFixedBy
, untilFixedM
, mapFst
, mapSnd
, commonPrefix
, replaceOne
, replaceAll
) where

-- Yields the result of applying f until a fixed point is reached.
untilFixedBy :: (a -> a -> Bool) -> (a -> a) -> a -> a
untilFixedBy eq f x = fst . head . filter (uncurry eq) $
        zip (iterate f x) (tail $ iterate f x)

untilFixed :: (Eq a) => (a -> a) -> a -> a
untilFixed = untilFixedBy (==)

-- Note that we apply until the entire "monadic environment" is fixed, not just
-- until the value in the monad is fixed.
untilFixedM :: (Eq (m a), Monad m) => (a -> m a) -> a -> m a
untilFixedM f x = untilFixed (>>=f) (return x)


-- Apply functions across 1st and 2nd in tuple
mapFst :: (a -> b) -> (a,c) -> (b,c)
mapFst f (x,y) = (f x, y)

mapSnd :: (a -> b) -> (c,a) -> (c,b)
mapSnd f (x,y) = (x, f y)

-- Find common prefix of list of lists. This algorithm sucks but at least it
-- was easy to write.
commonPrefix :: (Eq a) => [[a]] -> [a]
commonPrefix [] = []
commonPrefix ([]:_) = []
commonPrefix xss@((x:_):_) = if and $ map (\xs' ->
                                            not (null xs') && x == head xs')
                                          xss
                                then x:(commonPrefix $ map tail xss)
                                else []
-- Find / replace elements in a list
replaceOne :: (Eq a) => a -> a -> [a] -> [a]
replaceOne _ _ [] = []
replaceOne x x' (y:ys) | x == y = (x':ys)
                       | otherwise = (y:replaceOne x x' ys)

replaceAll :: (Eq a) => a -> a -> [a] -> [a]
replaceAll x x' = map f
    where f y | x == y    = x'
          f y | otherwise = y

replaceAllL :: (Eq a) => a -> [a] -> [a] -> [a]
replaceAllL x xs' = concat . map f
    where f y | x == y    = xs'
          f y | otherwise = [y]

