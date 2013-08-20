{-
import Data.Array
import Data.Tree
import Data.List
-}
import qualified Data.Map.Lazy as M
import qualified Data.Maybe as Maybe
import qualified Control.Monad as Monad
import qualified Data.Graph as Graph
import Control.Exception.Base (assert)

-- Some really general things we use:

-- Yields the result of applying f until a fixed point is reached.
untilFixed :: (Eq a) => (a -> a) -> a -> a
untilFixed f x = fst . head . filter (uncurry (==)) $
        zip (iterate f x) (tail $ iterate f x)

-- A SpineGraph represents a graph which is embedded as the spine of a surface,
-- keeping track of the data necessary to:
-- (1) Implement the Bestvina-Handel algorithm
-- (2) Display the resulting fibered surface / train track

-- As in Toby Hall's program "Trains", we need to store data on each vertex
-- (the zone of the surface it's located in, and the cyclic order of its
-- incident edges) and each edge (its endpoints, and the zones of the surface
-- it traverses). The surface is divided into "zones" around punctures /
-- boundaries / etc.
-- We represent the graph as an adjacency list AND an incidence list. Any
-- updates to the graph need to keep all these components in sync.
-- [BH] G

-- Note that all ID types must be instances of Ord so they can be used as keys
-- in a Data.Map.Lazy.Map
newtype VertexID = VertexID { vertexID :: Int }
    deriving (Show,Eq,Ord)
newtype EdgeID   = EdgeID   { edgeID   :: Int }
    deriving (Show,Eq,Ord)
newtype ZoneID   = ZoneID   { zoneID   :: Int }
    deriving (Show,Eq,Ord)

data Dir = Fwd | Back -- Direction of traversal/orientation of an edge
    deriving (Show,Eq)

rev :: Dir -> Dir
rev Fwd = Back
rev Back = Fwd


data SpineVertex = SpineVertex
    { incidentEdges :: [EdgeID] -- in cyclic order in the embedded graph
    , incidentDirs  :: [Dir] -- Fwd if this vertex is 1st vertex of the edge,
                             -- Back if 2nd vertex
    , vertexZone    :: ZoneID }
    deriving (Show,Eq)
-- If an edge has both endpoints at a single vertex, the edge is listed twice
-- in the incident edge list (once Fwd and once Back)

-- Note that edges are undirected. Each edge ID will be listed among the
-- incident edges of both its start and end vertices. BUT when it comes to
-- things that require an edge orientation (like map of edges in GraphMap) we
-- use the first -> second orientation by convention in the map.
data SpineEdge = SpineEdge
    { firstVertex    :: VertexID
    , secondVertex   :: VertexID
    , traversedZones :: [ZoneID] }
    deriving (Show,Eq)

data SpineGraph = SpineGraph
    { vertexData :: M.Map VertexID SpineVertex
    , edgeData   :: M.Map EdgeID SpineEdge }
    deriving (Show,Eq)

-- Directed edge = edge + direction to traverse in
data DEdge = DEdge EdgeID Dir
    deriving (Show,Eq)

-- Get the directed endpoints (start,end) of a given edge.
dirEndpoints :: SpineGraph -> DEdge -> Maybe (VertexID,VertexID)
dirEndpoints (SpineGraph _ edata) (DEdge e d) = do
    SpineEdge v1 v2 _ <- M.lookup e edata
    return (case d of Fwd  -> (v1,v2)
                      Back -> (v2,v1))


vertices :: SpineGraph -> [VertexID]
vertices = M.keys . vertexData

edges :: SpineGraph -> [EdgeID]
edges = M.keys . edgeData

isConsistent :: SpineGraph -> Bool
isConsistent (SpineGraph vdata edata) = Maybe.isJust $ do
     Monad.forM_ (M.keys edata) checkEndpoints
     Monad.forM_ (M.keys vdata) checkIncEdges
     where checkEndpoints :: EdgeID -> Maybe ()
           checkEndpoints eid = do
               SpineEdge v1id v2id zs <- M.lookup eid edata
               -- Check that both endpoints of each edge exist...
               SpineVertex _ _ z1 <- M.lookup v1id vdata
               SpineVertex _ _ z2 <- M.lookup v2id vdata
               -- ... and have the same zones as start/end zones of the edge
               ez1 <- Maybe.listToMaybe zs
               guard $ z1 == ez1 && z2 == last zs
           checkIncEdges :: VertexID -> Maybe ()
           checkIncEdges vid = do
               SpineVertex ies dirs _ <- M.lookup vid vdata
               Monad.zipWithM_ checkIncEdge ies dirs
               where checkIncEdge eid dir = do
                   -- Check that all incident edges of each vertex exist...
                   SpineEdge v1id v2id _ <- M.lookup eid edata
                   -- ... and have that vertex as a start or end vertex
                   guard $ (v1id == vid && dir == Fwd) ||
                           (v2id == vid && dir == Back)

-- Convert a SpineGraph into a Data.Graph.Graph by forgetting lots of stuff. We
-- produce a directed graph with 2 edges for each undirected edge in the
-- original graph (so dfs, etc. will work correctly).
toAbstractGraph :: SpineGraph -> Graph.Graph
toAbstractGraph (SpineGraph vdata edata) = Graph.buildG (minvid, maxvid) es
    where es   = (map (\(SpineEdge (VertexID v1) (VertexID v2) _) -> (v1,v2)) $
              M.elems edata) ++
                 (map (\(SpineEdge (VertexID v1) (VertexID v2) _) -> (v2,v1)) $
              M.elems edata)
          vids = map vertexID $ M.keys vdata
          minvid = minimum vids
          maxvid = maximum vids

-- Represents a path of edges. For each edge we indicate whether we traverse it
-- forwards or backwards.
-- Note that an edge can map to the empty path, in which case we need to look
-- up its endpoints to figure out what vertex it's actually "sitting on"
type Path = [DEdge]

pathStart :: Path -> Maybe VertexID
pathStart [] = Nothing
pathStart p  = Monad.liftM fst $ dirEndpoints (head p)

pathEnd :: Path -> Maybe VertexID
pathEnd [] = Nothing
pathEnd p  = Monad.liftM snd $ dirEndpoints (last p)

isConsistentPath :: Path -> Bool
isConsistentPath [] = True
isConsistentPath p  = Maybe.isJust $ zipWithM_ checkPair p (tail p)
    where checkPair de1 de2 = do
              -- end of each edge is start of the next
              (v11,v12) <- dirEndpoints de1
              (v21,v22) <- dirEndpoints de2
              guard $ v12 == v21

-- Map sends vertices to vertices, and edges to edge paths.
-- [BH] g: G -> G
data GraphMap = GraphMap
    { graphToMap :: SpineGraph
    , vertexMap  :: M.Map VertexID VertexID
    , edgeMap    :: M.Map EdgeID Path }
    deriving (Show,Eq)

vertexPreimage :: GraphMap -> VertexID -> [VertexID]
vertexPreimage (GraphMap _ vmap _) v = M.keys $ M.filter (== v) vmap

isConsistentMap :: GraphMap -> Bool
isConsistentMap (GraphMap sg@(SpineGraph vdata edata) vmap emap) =
    isConsistent sg &&
    -- Maps are defined for all vertices / edges
    M.keysSet vdata == M.keysSet vmap &&
    M.keysSet edata == M.keysSet emap &&
    (Maybe.isJust $ do
        -- Each vertex maps to a well-defined vertex
        Monad.forM_ (M.elems vmap) (\v -> M.lookup v vdata)
        -- Each edge maps to a well-defined consistent edge path
        Monad.forM_ (M.keys emap) checkEdge)
    where checkEdge e = do
            (SpineEdge v1 v2 _) <- M.lookup e edata
            gv1 <- M.lookup v1 vmap
            gv2 <- M.lookup v2 vmap
            path <- M.lookup e emap
            case path of
                 []        -> guard $ gv1 == gv2
                 otherwise -> do
                     p1 <- pathStart path
                     p2 <- pathEnd path
                     guard $ gv1 == p1 && gv2 == p2
            guard $ isConsistentPath path




-- Map manipulation helper functions.

-- Isotope the given map by pulling the image of the given vertex across the
-- given edge and "dragging" the images of all edges incident to that vertex
-- along with it. That is, given a vertex (v) and edge (v1,v2) satisfying
-- g(v)=v1, we isotope g to g' st g'(v)=v2.
--
-- Note that this NOT does correct for edges whose images "double back after
-- pulling". i.e., given an edge (w,v) incident to v on the left, if g sends
-- this edge to a path terminating in (v2,v1), we will still add the additional
-- step (v1,v2) onto the image of the edge (w,v)
--
-- Error if the ids are invalid or the above condition is false.
isoVertex :: DEdge -> VertexID -> GraphMap -> GraphMap
isoVertex de@(DEdge e dir) v (GraphMap sg@(SpineGraph vdata edata) vmap emap)
    = GraphMap sg newvmap newemap
    where (SpineVertex ies dirs _)  = Maybe.fromJust $ M.lookup v vdata
          (v1,v2)                   = Maybe.fromJust $ dirEndpoints sg de
          -- Vertex (which mapped to v1) now maps to v2
          newvmap = assert (v1 == (Maybe.fromJust $ M.lookup v vmap)) $
              M.insert v v2 vmap
          -- Each incident edge maps to a path with one additional step
          -- If the edge goes out of v, we add (v2,v1) to the front
          -- if into v, we add (v1,v2) to the back.
          newemap = foldr adjustEdge emap (zip ies dirs)
          adjustEdge :: (EdgeID, Dir) -> M.Map EdgeID Path -> M.Map EdgeID Path
          adjustEdge (ie,d) = case d of
                                   Fwd  -> M.adjust ([DEdge e (rev dir)] ++) ie
                                   Back -> M.adjust (++ [DEdge e dir]) ie

-- Isotope the given map by postcomposing with an isotopy "pulling the given
-- edge's start vertex across itself". That is, apply the earlier isotopy to
-- all preimages of the given edge's starting vertex.

-- Similarly, error if edge not present.
isoVertexRight :: DEdge -> GraphMap -> GraphMap
isoVertexRight de g@(GraphMap sg _ _) =
    foldr (isoVertex de) g (vertexPreimage g v)
    where (v,_) = Maybe.fromJust $ dirEndpoints sg de

-- Return a path which does not backtrack, by removing all parts of the path
-- which double back on themselves.
-- This algorithm is grotesquely inefficient.
deBacktrack :: Path -> Path
deBacktrack = untilFixed deBacktrackPair
    where -- Remove the last matching backtracking pair of path components,
          -- e.g. given path (e1 Fwd),(e1 Back),(e2 Back),(e2 Fwd),(e2 Back),
          -- the last two path components will be removed.
          deBacktrackPair :: Path -> Path
          deBacktrackPair [] = []
          deBacktrackPair [de] = [de]
          deBacktrackPair (de1@(DEdge e1 d1):de2@(DEdge e2 d2):des)
            | e1 == e2 && d1 == rev d2 = des
            | otherwise                = de1:de2:(deBacktrackPair des)

-- Return all edges which are fixed under the given map.
invariantEdges :: GraphMap -> [EdgeID]
invariantEdges (GraphMap _ _ emap) = filter isInv $ M.keys emap
    where isInv e = [(e,Fwd) == Maybe.fromJust (M.lookup e emap)]



-- Implementations of the fibered surface moves.
-- 1. Collapse invariant forest
-- Find fixed vertices/edges, build forests from these, flatten them into
-- bunches of vertices / edges to be collapsed, check to make sure they're
-- non-overlapping, then collapse them.

-- 2. Valence 1 isotopy
-- Find a valence 1 vertex


{-

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
-}
main :: IO ()
main = print "TODO XXX"
