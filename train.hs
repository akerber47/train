import Data.Array
import Data.Graph
import Data.Tree
import Data.List
import qualified Data.Map.Lazy as M

-- Represents a graph which is the spine of a (fibered) surface. Note that the
-- adjacency lists are stored in cyclic order (as in Toby Hall's Trains program)
-- for the Bestvina-Handel algorithm. We also keep track of the "zones" (regions
-- in the surface) that each edge travels through, in order. We'll store the
-- surface and its zones with a (fixed) representation later. Note that we don't
-- need to store the zone data of the vertices as this is easy to recover from
-- the zone data on the edges.
-- By convention, since our graphs are undirected, we store all edges pointing
-- in both directions, so builtin functions like dfs, etc. work correctly. This
-- means that any fixed-edge filtering operation, spine graph constructor, etc.
-- will consume/produce this duplicate data.
-- Finally, note that there may be multiple edges between any pair of vertices
-- (that is, our graph may not be simple). We represent this by storing the same
-- vertex multiple times in the adjacency list.
-- [BH] G
type Zone = Int
type SpineGraph = M.Map Vertex [(Vertex, [Zone])]

-- Edge in a SpineGraph, with zone data.
type SpineEdge = (Vertex, Vertex, [Zone])

-- Convert a SpineGraph into a Data.Graph.Graph by forgetting zone data, and
-- converting the Map into an Array.
toGraph :: SpineGraph -> Graph
toGraph sg = fmap (map fst) $
    array (fst $ M.findMin sg, fst $ M.findMax sg) (M.toList sg)

-- Convert a SpineEdge into a Data.Graph.Edge by forgetting zone data
toEdge :: SpineEdge -> Edge
toEdge (v1,v2,zs) = (v1,v2)

sgVertices :: SpineGraph -> [Vertex]
sgVertices = M.keys

-- Incidence list (with zone data) of SpineGraph. Note that this loses cyclic
-- order of edges incident at each vertex.
sgEdges :: SpineGraph -> [SpineEdge]
sgEdges sg = concat [[(v1,v2,zs) | (v2,zs) <- vzs] | (v1,vzs) <- M.toList sg]

-- Map sends vertices to vertices, and edges to edge paths.
-- Maps implemented with Data.Map (dicts) for ease of updating (with insert).
-- Note that arrays don't work so well bc SpineEdges lack good Ix behavior.
-- [BH] g: G -> G
type GraphMap = (SpineGraph, M.Map Vertex Vertex, M.Map SpineEdge [SpineEdge])

-- Link of vertex is precisely the adjacency list
-- Returns Nothing if vertex is not in graph
-- [BH] Lk(v, G)
link :: SpineGraph -> Vertex -> Maybe [Vertex]
link sg v = do vzs <- M.lookup v sg
               return $ map fst vzs

-- Derivative of map
-- [BH] Dg(v) : d \in Lk(v,G) |-> Dg(d) \in Lk(g(v),G)
derivative :: GraphMap -> SpineEdge -> SpineEdge
derivative (_,_,emap) e = head $ emap M.! e


-- Implementations of the fibered surface moves.
-- 1. Collapse invariant forest
-- Find fixed vertices/edges, build forests from these, flatten them into
-- bunches of vertices / edges to be collapsed, check to make sure they're
-- non-overlapping, then collapse them.

collapse :: GraphMap -> GraphMap
collapse g@(sg, vmap, emap) = foldl collapseTree g nubInvForest
    where invVertices  = filter (\v -> v == vmap M.! v) $ sgVertices sg
          invEdges     = filter (\e -> [e] == emap M.! e) $ sgEdges sg
          invForest   :: [Tree Vertex]
          invForest    = dfs invVertices $ buildG (vertices sg) invEdges
          -- Remove overlaps to get nubInvForest
          -- Note that "overlapping" is not actually an equivalence (it's not
          -- transitive) so nubBy may accidentally remove too many elements from
          -- this list. But that's ok bc collapse is not guaranteed to collapse
          -- the largest possible invariant forest anyways.
          nubInvForest = nubBy (\t1 t2 -> not $ null $
                          intersect (flatten t1) (flatten t2)) invForest
          -- Remove the given tree from the graph (map), replacing it with a
          -- single vertex. This is tricky bc we need to keep get the cyclic
          -- order correct at the new (collapsed) vertex.
          collapseTree :: GraphMap -> Tree Vertex -> GraphMap
          collapseTree g (Node v []) = g -- trivial (one-vertex) case

-- Sums primes up to nth (yay lazy evaluation!)
sumPrimesTo :: Integer -> Integer
sumPrimesTo n = sieve [2..] 0
    where sieve (p:ms) sumacc | p >= n = sumacc
                              | p < n  = sieve (filter (\m -> m `mod` p /= 0) ms) (p+sumacc)

main :: IO ()
main = print $ sumPrimesTo 2000000
{-
import Data.List

-- Same factorization algorithm as from #3
-- Kind of stupid to use it here as it's totally stateless and will sieve
-- repeatedly (herp derp).

-- Pick out which primes divide the given integer.
-- Helper uses accfactors for tail recursion.
-- Takes in number to factor, list of things that are possibly primes (to check
-- against), and factor accumulator list.
-- For efficiency we only sieve the possible prime list as we need to.
factors :: Int -> [Int]
factors n =  factorHelper n [2..n] []
    where sieve :: Int -> [Int] -> [Int]
          sieve p ps = filter (\m -> m `mod` p /= 0) ps
          factorHelper :: Int -> [Int] -> [Int] -> [Int]
          factorHelper 1 _      accfactors = accfactors
          factorHelper m []     accfactors = (m:accfactors)
          factorHelper m (p:ps) accfactors | m `mod` p == 0 = factorHelper (m `div` p) (p:ps) (p:accfactors)
                                           | otherwise      = factorHelper m (sieve p ps) accfactors

-- Counts divisors of a number (standard trick w/ prime factorization)
countDivs :: Int -> (Int, Int)
countDivs n = (n,product $ map (+1) facCounts)
    where facs      = factors n
          facCounts = map (\i -> length $ filter (== i) facs) $ nub facs

main :: IO ()
main = print $ fst $ head $ dropWhile ((< 500) . snd) triDivs
    where triDivs = map (countDivs . (\n -> n*(n+1)`div`2)) $ [5..]
-- Trimmed all numbers to first 20 digits, definitely enough

main :: IO ()
main = print $ sum $ nums
    where nums :: [Integer]
          nums = [
		3710728753390210279,
		4637693767749000971,
		7432498619952474105,
		9194221336357416157,
		2306758820753934617,
		8926167069662363382,
		2811287981284997940,
		4427422891743252032,
		4745144573600130643,
		7038648610584302543,
		6217645714185656062,
		6490635246274190492,
		9257586771833721766,
		5820356532535939900,
		8018119938482628201,
		3539866437282711265,
		8651550600629586486,
		7169388870771546649,
		5437007057682668462,
		5328265410875682844,
		3612327252500029607,
		4587657617241097644,
		1742370690585186066,
		8114266041808683061,
		5193432545172838864,
		6246722164843507620,
		1573244438690812579,
		5503768752567877309,
		1833638482533015468,
		8038628759287849020,
		7818283375799310361,
		1672632010043689784,
		4840309812907779179,
		8708698755139271185,
		5995940689575653678,
		6979395067965269474,
		4105268470829908521,
		6537860736150108085,
		3582903531743471732,
		9495375976510530594,
		8890280257173322961,
		2526768027607800301,
		3627021854049770558,
		2407448690823117497,
		9143028819710328859,
		3441306557801612781,
		2305308117281643048,
		1148769693215490281,
		6378329949063625966,
		6772018697169854431,
		9554825530026352078,
		7608532713228572311,
		3777424253541129168,
		2370191327572567528,
		2979886027225833191,
		1849570145487928898,
		3829820378303147352,
		3482954382919991818,
		4095795306640523263,
		2974615218550237130,
		4169811622207297718,
		6246795719440126904,
		2318970677254791506,
		8618808822587531452,
		1130673970830472448,
		8295917476714036319,
		9762333104481838626,
		4284628018351707052,
		5512160354698120058,
		3223819573432933994,
		7550616496518477518,
		6217784275219262340,
		3292418570714734956,
		9951867143023521962,
		7326746080059154747,
		7684182252467441716,
		9714261791034259864,
		8778364618279934631,
		1084880252167467088,
		7132961247478246453,
		6218407357239979422,
		6662789198148808779,
		6066182629368283676,
		8578694408955299065,
		6602439640990538960,
		6491398268003297315,
		1673093931987275027,
		9480937724504879515,
		7863916702118749243,
		1536871371193661495,
		4078992311553556256,
		4488991150144064802,
		4150312888033953605,
		8123488067321014673,
		8261657077394832759,
		2291880205877731971,
		7715854250201654509,
		7210783843506918615,
		2084960398013400172,
		5350353422647252425]
-- Project Euler: Problem 1

nums :: [Integer]
nums = 1:map (+1) nums
natmult :: [Integer]
natmult = filter (\x -> (mod x 3) == 0 || (mod x 5) == 0) nums
natless :: [Integer]
natless = filter (< 1000) (take 1000 natmult)

main :: IO ()
main = print $ sum natless
fibsumHelper :: (Integral a) => a -> a -> a -> a
fibsumHelper 0 _ _ = 0
fibsumHelper 1 _ _ = 1
fibsumHelper n i j = if i <= n
                      then if (even i)
                              then i+(fibsumHelper n (i+j) i)
                              else fibsumHelper n (i+j) i
                      else 0
fibsum :: Integer -> Integer
fibsum n = fibsumHelper n 1 1

main :: IO ()
main = print $ fibsum 4000000
-- This algorithm sucks less than before

-- Pick out which primes divide the given integer.
-- Helper uses accfactors for tail recursion.
-- Takes in number to factor, list of things that are possibly primes (to check
-- against), and factor accumulator list.
-- For efficiency we only sieve the possible prime list as we need to.
factors :: Integer -> [Integer]
factors n =  factorHelper n [2..n] []
    where sieve :: Integer -> [Integer] -> [Integer]
          sieve p ps = filter (\m -> m `mod` p /= 0) ps
          factorHelper :: Integer -> [Integer] -> [Integer] -> [Integer]
          factorHelper 1 _      accfactors = accfactors
          factorHelper m []     accfactors = (m:accfactors)
          factorHelper m (p:ps) accfactors | m `mod` p == 0 = factorHelper (m `div` p) (p:ps) (p:accfactors)
                                           | otherwise      = factorHelper m (sieve p ps) accfactors

main :: IO ()
main = print $ maximum $ factors 600851475143
-- Number assumed to have 6 digits
isPal :: Int -> Bool
isPal n = d1 == d6 && d2 == d5 && d4 == d3
    where d1 = n `mod` 10
          d2 = n `mod` 100 `div` 10
          d3 = n `mod` 1000 `div` 100
          d4 = n `mod` 10000 `div` 1000
          d5 = n `mod` 100000 `div` 10000
          d6 = n `div` 100000

-- List of all possible digits of 2 3-digit #s
possiblePals :: [Int]
possiblePals = [a*b | a <- [100..999], b <- [100..999]]
                            
main :: IO ()
main = print $ maximum $ filter isPal possiblePals
-- Um just use prime factors
ans :: Integer
ans = 2*2*2*2*3*3*5*7*11*13*17*19

main :: IO ()
main = print ans
-- Um just use sum formulas
ans :: Integer
ans = ((100*101) `div` 2)*((100*101) `div` 2) - ((100*101*201) `div` 6)

main :: IO ()
main = print ans

-- Gets nth prime (yay lazy evaluation!)
getPrime :: Integer -> Integer
getPrime n = sieve [2..] n
    where sieve (p:ms) 1 = p
          sieve (p:ms) k = sieve (filter (\m -> m `mod` p /= 0) ms) (k-1)

main :: IO ()
main = print $ getPrime 10001
-- Can get Pythagorean triplets via 2ab, a^2-b^2,a^2+b^2 trick

-- Brute-force some values of a and b

main :: IO ()
main = print answer
    where possibleTrips :: [(Int,Int)]
          possibleTrips = [(a,b) | a <- [1..500], b <- [1..500]]
          passedTrips = filter (\(a,b) -> a>b && (2*a*b)+(a*a-b*b)+(a*a+b*b) == 1000) possibleTrips
          x = fst $ head passedTrips
          y = snd $ head passedTrips
          answer = (2*x*y)*(x*x-y*y)*(x*x+y*y)

-}
