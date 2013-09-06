import qualified Data.List as List
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


-- Data associated with a vertex in the spine graph.
data SpineVertex = SpineVertex
    { incidentEdges :: [EdgeID] -- in cyclic order in the embedded graph
    , incidentDirs  :: [Dir] -- Fwd if this vertex is 1st vertex of the edge,
                             -- Back if 2nd vertex
    , vertexZone    :: ZoneID }
    deriving (Show,Eq)
-- If an edge has both endpoints at a single vertex, the edge is listed twice
-- in the incident edge list (once Fwd and once Back)

-- Data associated with an edge in the spine graph.
-- Note that edges are undirected. Each edge ID will be listed among the
-- incident edges of both its start and end vertices. BUT when it comes to
-- things that depend on edge orientation (like map of edges in GraphMap) we
-- use the first -> second orientation by convention.
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
-- Get the directed zones of a given edge.
dirZones :: SpineGraph -> DEdge -> Maybe [ZoneID]
dirZones (SpineGraph _ edata) (DEdge e d) = do
    SpineEdge _ _ zs <- M.lookup e edata
    return (case d of Fwd  -> zs
                      Back -> reverse zs)

-- Create a DEdge outgoing from the given vertex and traversing the given edge.
-- If the given vertex is not an endpoint of the edge, error.
toOutgoing :: SpineGraph -> EdgeID -> VertexID -> DEdge
toOutgoing (SpineGraph _ edata) e v = assert (v == v1 || v == v2) $
    (DEdge e dir)
    where (SpineEdge v1 v2 _) = edata M.! e
          dir = if v == v1 then Fwd else Back

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
               Monad.guard $ z1 == ez1 && z2 == last zs
           checkIncEdges :: VertexID -> Maybe ()
           checkIncEdges vid = do
               SpineVertex ies dirs _ <- M.lookup vid vdata
               Monad.zipWithM_ checkIncEdge ies dirs
               where checkIncEdge eid dir = do
                         -- Check that each incident edge exists...
                         SpineEdge v1id v2id _ <- M.lookup eid edata
                         -- ... and have that vertex as a start or end vertex
                         Monad.guard $ (v1id == vid && dir == Fwd) ||
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

-- Collapse the given edge in the graph. We collapse the edge (v1,v2) "fwd"
-- (that is, v1 is removed from the graph, and all edges incident to v1 are
-- pulled to be incident to v2, adjusting zones and cyclic orders accordingly)
collapseEdge :: DEdge -> SpineGraph -> SpineGraph
collapseEdge de@(DEdge e d) sg@(SpineGraph vdata edata) =
        SpineGraph newvdata newedata
    where (v1,v2) = Maybe.fromJust $ dirEndpoints sg de
          SpineVertex v1ies v1ieds v1z = vdata M.! v1
          SpineVertex v2ies v2ieds v2z = vdata M.! v2
          -- Build new graph:
          -- 1. Modify the data of all edges incident to v1 to
          -- instead have v2 as a vertex, and modifying their zone lists
          -- accordingly
          newedata = foldl pullEdge edata $ zip v1ies v1ieds
          pullEdge edata' (e',d') =
              case d' of
                   Back ->
                       -- v1 was the 2nd vertex of edge e'
                       M.insert e' (SpineEdge e1 v2 $ ezs++zs) edata'
                   Fwd  ->
                       -- v1 was the 1st vertex of edge e'
                       M.insert e' (SpineEdge v2 e2 $ (reverse zs)++ezs) edata'
              where SpineEdge e1 e2 ezs = edata M.! e
                    zs = Maybe.fromJust $ dirZones sg de
          -- 2. Modify incidence list at v2 to include pulled edges, inserting
          -- them at the location of the collapsed edge in the cyclic order.
          -- Also, remove v1 from vertices
          newvdata = M.insert v2 (SpineVertex newies newieds v2z) $
              M.delete v1 vdata
              where ix1 = Maybe.fromJust $ List.elemIndex e v1ies
                    ix2 = Maybe.fromJust $ List.elemIndex e v2ies
                    -- The incident edge at v1 "after" (v1,v2) in cyclic order
                    -- is pulled to immediately "after"
                    -- the incident edge at v2 "before" (v1,v2)
                    -- (Draw a picture, it makes sense)
                    newies = (take ix2 v2ies) ++
                             (drop (ix1+1) v1ies) ++
                             (take ix1 v1ies) ++
                             (drop (ix2+1) v2ies)
                    -- Dirs follow same pattern
                    newieds = (take ix2 v2ieds) ++
                              (drop (ix1+1) v1ieds) ++
                              (take ix1 v1ieds) ++
                              (drop (ix2+1) v2ieds)

------------------------------------------------------------------------------
------------------------------------------------------------------------------
------------------------------------------------------------------------------

-- Represents a path of edges. For each edge we indicate whether we traverse it
-- forwards or backwards.
-- Note that an edge can map to the empty path, in which case we need to look
-- up its endpoints to figure out what vertex it's actually "sitting on"
type Path = [DEdge]

-- Represents a tree of vertices/edges in a SpineGraph. All edges point "down".
-- This needs to be a list of trees bc there may be multiple edges out of
-- root vertex - these will be the "root edges"
type Tree = [Graph.Tree DEdge]

-- Represents a tree of edges in a SpineGraph. All edges point "down". This has
-- a "root edge" rather than a root vertex
type ETree = Graph.Tree DEdge

pathStart :: SpineGraph -> Path -> Maybe VertexID
pathStart _ [] = Nothing
pathStart sg p = Monad.liftM fst $ dirEndpoints sg (head p)

pathEnd :: SpineGraph -> Path -> Maybe VertexID
pathEnd _ [] = Nothing
pathEnd sg p = Monad.liftM snd $ dirEndpoints sg (last p)

revPath :: Path -> Path
revPath p = reverse [(DEdge e (rev d)) | (DEdge e d) <- p]

isConsistentPath :: SpineGraph -> Path -> Bool
isConsistentPath _ [] = True
isConsistentPath sg p = Maybe.isJust $ Monad.zipWithM_ checkPair p (tail p)
    where checkPair de1 de2 = do
              -- end of each edge is start of the next
              (v11,v12) <- dirEndpoints sg de1
              (v21,v22) <- dirEndpoints sg de2
              Monad.guard $ v12 == v21

------------------------------------------------------------------------------
------------------------------------------------------------------------------
------------------------------------------------------------------------------

-- Map sends vertices to vertices, and edges to edge paths. By convention each
-- edge is oriented in the fwd direction (1st vertex to 2nd vertex) when
-- describing the map of edges to (oriented) edge paths.
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
                 -- Empty path stays at a single vertex
                 [] -> Monad.guard $ gv1 == gv2
                 p  -> do
                     -- Nonempty path has correct endpoints
                     p1 <- pathStart sg path
                     p2 <- pathEnd sg path
                     Monad.guard $ gv1 == p1 && gv2 == p2
            -- Interior edges of path line up consistently
            Monad.guard $ isConsistentPath sg path

-- Derivative of map at given oriented edge, as in Bestvina-Handel.
-- Nothing if edge collapses.
derivative :: GraphMap -> DEdge -> Maybe DEdge
derivative (GraphMap _ _ emap) (DEdge e d) =
    case d of Fwd  -> Maybe.listToMaybe $ p
              Back -> Maybe.listToMaybe $ revPath p
    where p = emap M.! e

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
    where (SpineVertex ies dirs _)  = vdata M.! v
          (v1,v2)                   = Maybe.fromJust $ dirEndpoints sg de
          -- Vertex (which mapped to v1) now maps to v2
          newvmap = assert (v1 == (vmap M.! v)) $
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
invariantEdges g@(GraphMap _ _ emap) = filter (isInvariant g) $ M.keys emap

isInvariant :: GraphMap -> EdgeID -> Bool
isInvariant g@(GraphMap _ _ emap) e =
    [(DEdge e Fwd)] == emap M.! e

------------------------------------------------------------------------------
------------------------------------------------------------------------------
------------------------------------------------------------------------------

-- Implementations of the fibered surface moves.

-- 1. Collapse an edge which is invariant under the given map. If edge is not
-- invariant, error.
collapseInvEdge :: DEdge -> GraphMap -> GraphMap
collapseInvEdge de@(DEdge e d) g@(GraphMap sg vmap emap) =
    assert (isInvariant g e && v1 /= v2) $
        GraphMap newsg newvmap newemap
    where newsg = collapseEdge de sg
          -- Build new map:
          (v1,v2) = Maybe.fromJust $ dirEndpoints sg de
          -- 3. Remove v1 from vertex map
          newvmap = M.delete v1 vmap
          -- 4. Remove collapsed edge from all paths that edges map to
          -- Also, remove collapsed edge from edge map
          newemap = M.map (filter $ \(DEdge e' _) -> e' /= e) $ M.delete e emap

-- Determines whether the invariant edges of the graph contain a cyclic path.
-- If so, return such a path. If not, return the invariant forest we built
-- up while "trying" to find a cycle.
findInvCycleOrForest :: GraphMap -> Either Path [Tree]
findInvCycleOrForest g@(GraphMap sg@(SpineGraph vdata edata) vmap emap) =
    Left [] -- TODO
    where ies = invariantEdges g
          -- Perform depth-first search starting at the tail of the given
          -- DEdge, searching only invariant edges and stopping at any vertex
          -- on the given list of visited vertices. If we visit a vertex more
          -- than once, found a cycle.
          -- Return the new (longer) list of visited vertices, and either the
          -- path to an already-visited vertex (if we hit one) or the tree of
          -- edges we built up (if not).
          dfs :: DEdge -> [VertexID] -> ([VertexID], Either Path ETree)
          dfs de@(DEdge e d) vs = ([], Left []) -- TODO
            where (_,v) = Maybe.fromJust $ dirEndpoints sg de
                  SpineVertex es _ _ = vdata M.! v
                  esToTraverse = List.delete e es



-- 2. Remove a valence 1 vertex via isotopy.


-- 3. Remove a valence 2 vertex via isotopy.

-- 4. Pull the map tight.


main :: IO ()
main = print "TODO XXX"
