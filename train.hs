import qualified Data.List as List
import qualified Data.Map.Lazy as M
import qualified Data.Set as S
import qualified Data.Maybe as Maybe
import qualified Control.Monad as Monad
import qualified Data.Graph as Graph

import Control.Exception.Base (assert)

-- Some really general things we use:

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

-- Insert given tree (2nd arg) in as child of given node of another tree (1st)
-- inserts after all other children of that node.
insertSubtree :: Graph.Tree a -> Graph.Tree a -> Graph.Tree a
insertSubtree (Graph.Node x ts) t = Graph.Node x (ts ++ [t])

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

-- Returns the maximum member of the (first) set in the given list of sets
-- which contains the given element. Because I am too lazy to implement
-- union-find properly.
setFind :: (Ord a) => [S.Set a] -> a -> a
setFind sets x = S.findMax . head . filter (S.member x) $ sets

-- A SpineGraph represents a graph which is embedded as the spine of a surface,
-- keeping track of the data necessary to:
-- (1) Implement the Bestvina-Handel algorithm
-- (2) Display the resulting fibered surface / train track

-- As in Toby Hall's program "Trains", we need to store data on each vertex
-- (the zone of the surface it's located in, and the cyclic order of its
-- incident edges) and each edge (its endpoints, and the zones of the surface
-- it traverses). The surface is divided into "zones" around punctures /
-- boundaries / etc.
-- By convention, cyclic orders are "counterclockwise from outside" wrt
-- implicit surface orientation.
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
    deriving (Show,Eq,Ord)

rev :: Dir -> Dir
rev Fwd = Back
rev Back = Fwd


-- TODO refactor to "outgoing incident edges"
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
    deriving (Show,Eq,Ord)

revDEdge :: DEdge -> DEdge
revDEdge (DEdge e d) = DEdge e (rev d)

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

-- Get the outgoing directed edges at a given vertex, in cyclic order.
-- Edge that loops back to the vertex will appear twice in the list.
outdes :: SpineGraph -> VertexID -> [DEdge]
outdes (SpineGraph vdata _) v = zipWith DEdge es ds
    where SpineVertex es ds _ = vdata M.! v

-- Create a DEdge outgoing from the given vertex and traversing the given edge.
-- If the given vertex is not an endpoint of the edge, error.
toOut :: SpineGraph -> VertexID -> EdgeID -> DEdge
toOut (SpineGraph _ edata) v e = assert (v == v1 || v == v2) $
    (DEdge e dir)
    where (SpineEdge v1 v2 _) = edata M.! e
          dir = if v == v1 then Fwd else Back

vertices :: SpineGraph -> [VertexID]
vertices = M.keys . vertexData

edges :: SpineGraph -> [EdgeID]
edges = M.keys . edgeData

-- Generate new IDs for vertices / edges to add to an existing graph.
newvid :: SpineGraph -> VertexID
newvid = VertexID . (+1) . vertexID . maximum . vertices

neweid :: SpineGraph -> EdgeID
neweid = EdgeID . (+1) . edgeID . maximum . edges

valence :: SpineGraph -> VertexID -> Int
valence (SpineGraph vdata edata) v = List.length es
    where SpineVertex es _ _ = vdata M.! v

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
          -- accordingly. Also, remove the given edge.
          newedata = foldl pullEdge (M.delete e edata) $ zip v1ies v1ieds
          pullEdge edata' (e',d') =
              case d' of
                   Back ->
                       -- v1 was the 2nd vertex of edge e'
                       M.insert e' (SpineEdge e1 v2 $ ezs++zs) edata'
                   Fwd  ->
                       -- v1 was the 1st vertex of edge e'
                       M.insert e' (SpineEdge v2 e2 $ (reverse zs)++ezs) edata'
              where SpineEdge e1 e2 ezs = edata M.! e'
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

-- Folds the (1st) given edge (v0,v1) in the graph onto the (2nd) given edge
-- (v0,v2) in the graph. Both edges must have the same starting vertex and
-- adjacent ending vertices in the cyclic order around the start vertex.
foldEdge :: DEdge -> DEdge -> SpineGraph -> SpineGraph
foldEdge de1@(DEdge e1 d1) de2@(DEdge e2 d2) sg@(SpineGraph vdata edata) =
        assert (v0 == v0') $
        assert (List.isInfixOf [e1,e2] v1ies || List.isInfixOf [e2,e1] v1ies) $
        SpineGraph newvdata newedata
    where (v0, v1) = Maybe.fromJust $ dirEndpoints sg de1
          (v0',v2) = Maybe.fromJust $ dirEndpoints sg de2
          SpineVertex v0ies _      _   = vdata M.! v0
          SpineVertex v1ies v1ieds _   = vdata M.! v1
          SpineVertex v2ies v2ieds v2z = vdata M.! v2
          e1zs = Maybe.fromJust $ dirZones sg de1
          e2zs = Maybe.fromJust $ dirZones sg de2
          -- Build new graph:
          -- 1. Modify the data of all edges incident to v1 to
          -- instead have v2 as a vertex, and modifying their zone lists
          -- accordingly. In order to fold the edges together, each edge
          -- formerly incident to v1 must traverse all zones traversed by
          -- (v0,v1) edge (in reverse order) followed by zones traversed by
          -- (v0,v2) edge - except for zones shared by both these edges. Also,
          -- remove (v0,v1) edge.
          commonzs = commonPrefix [e1zs,e2zs]
          newzs = (reverse $ e1zs List.\\ commonzs) ++ (e2zs List.\\ commonzs)
          newedata = foldl moveEdge (M.delete e1 edata) $ zip v1ies v1ieds
          moveEdge edata' (e',d') =
            case d' of
                 Back ->
                   -- v1 was the 2nd vertex of edge e'
                   M.insert e' (SpineEdge ev1 v2 $ ezs++newzs) edata'
                 Fwd  ->
                   -- v1 was the 1st vertex of edge e'
                   M.insert e' (SpineEdge v2 ev2 $ (reverse newzs)++ezs) edata'
            where SpineEdge ev1 ev2 ezs = edata M.! e'
          -- 2. Modify incidence list at v2 to include moved edges, inserting
          -- them above/below the location of the edge (v0,v2) in the cyclic
          -- order (depending on whether the edge (v0,v1) lies above or below
          -- the edge (v0,v2))
          -- Also, remove v1 from vertices.
          newvdata = M.insert v2 (SpineVertex newies newieds v2z) $
              M.delete v1 vdata
              where ix1 = Maybe.fromJust $ List.elemIndex e1 v1ies
                    ix2 = Maybe.fromJust $ List.elemIndex e2 v2ies
                    -- The incident edge at v1 "after" (v0,v1) in cyclic order
                    -- becomes "first" among all edges moved to v2. All edges
                    -- moved from v1 come (in a clump) after (v0,v2) if pushed
                    -- from below and before if pushed from above.
                    newies = if List.isInfixOf [e1,e2] v1ies
                                then (take ix2 v2ies) ++
                                     (drop (ix1+1) v1ies) ++
                                     (take ix1 v1ies) ++
                                     (drop ix2 v2ies)
                                else (take (ix2-1) v2ies) ++
                                     (drop (ix1+1) v1ies) ++
                                     (take ix1 v1ies) ++
                                     (drop (ix2-1) v2ies)
                    -- Dirs follow same pattern
                    newieds = if List.isInfixOf [e1,e2] v1ies
                                then (take ix2 v2ieds) ++
                                     (drop (ix1+1) v1ieds) ++
                                     (take ix1 v1ieds) ++
                                     (drop ix2 v2ieds)
                                else (take (ix2-1) v2ieds) ++
                                     (drop (ix1+1) v1ieds) ++
                                     (take ix1 v1ieds) ++
                                     (drop (ix2-1) v2ieds)

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

splitPath :: SpineGraph -> VertexID -> Path -> (Path,Path)
splitPath sg v p =
    (takeWhile ((/=v) . fst . Maybe.fromJust . dirEndpoints sg) p,
     dropWhile ((/=v) . fst . Maybe.fromJust . dirEndpoints sg) p)

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

-- Map directed edge to directed path
mapDEdge :: GraphMap -> DEdge -> Path
mapDEdge (GraphMap _ _ emap) (DEdge e d) =
    case d of Fwd  -> p
              Back -> revPath p
    where p = emap M.! e

-- Derivative of map at given oriented edge, as in Bestvina-Handel.
-- Nothing if edge collapses.
derivative :: GraphMap -> DEdge -> Maybe DEdge
derivative g = Maybe.listToMaybe . mapDEdge g

-- Inverse image of derivative at given oriented edge (and given preimage
-- vertex). Error if given vertex is not preimage of given edge's 1st vertex.
derivativePreimage :: GraphMap -> VertexID -> DEdge -> [DEdge]
derivativePreimage g@(GraphMap sg@(SpineGraph vdata _) _ _) v de =
    assert (elem v $ vertexPreimage g v1) $
        filter ((==(Just de)) . derivative g) outdes
    where (v1,v2) = Maybe.fromJust $ dirEndpoints sg de
          outdes = zipWith DEdge es ds
          SpineVertex es ds _ = vdata M.! v

-- All possible derivative preimages at given oriented edge.
fullDerivativePreimage :: GraphMap -> DEdge -> [(VertexID, [DEdge])]
fullDerivativePreimage g@(GraphMap sg _ _) de =
    map (\v -> (v,derivativePreimage g v de)) vs
    where vs = vertexPreimage g $ fst $ Maybe.fromJust $ dirEndpoints sg de

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
--
-- Similarly, error if edge not present.
isoVertexOnRight :: DEdge -> GraphMap -> GraphMap
isoVertexOnRight de g@(GraphMap sg _ _) =
    foldr (isoVertex de) g (vertexPreimage g v)
    where (v,_) = Maybe.fromJust $ dirEndpoints sg de

-- Isotope the given map so that all preimages of the given edge's starting
-- vertex are pulled across the given edge. Then collapse the given edge,
-- removing it and its 1st vertex from both graph and map.
isoAndCollapse :: DEdge -> GraphMap -> GraphMap
isoAndCollapse de@(DEdge e _) g@(GraphMap sg _ _) =
    GraphMap newsg newvmap newemap
    where -- Postcompose g with isotopy so that no vertex lands on 1st vertex.
          -- We can safely remove all copies of the given edge
          -- from paths edges map to (as the new paths will be isotopic to old)
          -- Also we remove this edge and vertex from the map.
          (v1,v2) = Maybe.fromJust $ dirEndpoints sg de
          GraphMap _ vmap emap = isoVertexOnRight de g
          newvmap = M.delete v1 vmap
          newemap = M.map (filter $ \(DEdge e' _) -> e' /= e) $ M.delete e emap
          -- Finally, remove the offending edge from the graph itself
          newsg = collapseEdge de sg


-- Return all vertices/edges which are fixed under the given map.
invariantVertices :: GraphMap -> [VertexID]
invariantVertices (GraphMap _ vmap _) = filter isInv $ M.keys vmap
    where isInv v = v == vmap M.! v

invariantEdges :: GraphMap -> [EdgeID]
invariantEdges g@(GraphMap _ _ emap) = filter (isInvariant g) $ M.keys emap

isInvariant :: GraphMap -> EdgeID -> Bool
isInvariant g@(GraphMap _ _ emap) e =
    [(DEdge e Fwd)] == emap M.! e

------------------------------------------------------------------------------
------------------------------------------------------------------------------
------------------------------------------------------------------------------

-- Implementations of the fibered surface moves.

---------- 2.1 ----------

-- Collapse an edge which is invariant under the given map. If edge is not
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

-- Collapse an entire forest of invariant vertices/edges. If forest is not
-- invariant, error.
collapseInvForest :: [Tree] -> GraphMap -> GraphMap
-- Note that a list of Trees is a list of lists of ETrees
collapseInvForest ts g = foldl (foldl collapseETree) g ts
    where collapseETree :: GraphMap -> ETree -> GraphMap
          -- Collapse outermost edges first, finishing with root edge.
          -- Edges in an ETree point outward, so need to reverse them.
          collapseETree tmpg (Graph.Node de ets) =
              collapseInvEdge (revDEdge de) $ foldl collapseETree tmpg ets

---------- 2.2 ----------

-- Remove a valence 1 vertex via isotopy. If the vertex is not valence 1, error
removeValenceOne :: VertexID -> GraphMap -> GraphMap
removeValenceOne v g@(GraphMap sg@(SpineGraph vdata _) _ _) =
    assert (valence sg v == 1) $
        isoAndCollapse outde g
    where SpineVertex es _ _ = vdata M.! v
          -- Find single outgoing edge, then collapse it
          outde@(DEdge e _) = toOut sg v $ head es

---------- 2.3 ----------

-- Remove a valence 2 vertex via isotopy. If the vertex is not valence 2, error
removeValenceTwo :: VertexID -> GraphMap -> GraphMap
removeValenceTwo v g@(GraphMap sg@(SpineGraph vdata _) _ _) =
    assert (valence sg v == 2) $
        isoAndCollapse outde1 g
    where SpineVertex es _ _ = vdata M.! v
          -- Find first outgoing edge, then collapse it
          -- (this will automatically pull 2nd edge "across the bridge")
          outde1@(DEdge e1 _) = toOut sg v $ head es


---------- 2.4 ----------

-- Two functions to pull the map tight.

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

-- Modify the map by isotopy so that derivative will not be constant at given
-- vertex (once paths are pulled tight / deBacktracked), by pulling its image
-- forward along the edge which is image of derivative.
deConstDerivative :: VertexID -> GraphMap -> GraphMap
deConstDerivative v g@(GraphMap sg@(SpineGraph vdata _) vmap emap)
    | commonPath == [] = g
    | otherwise        = GraphMap sg newvmap newemap
    where SpineVertex es ds _ = vdata M.! v
          outdes = zipWith DEdge es ds
          commonPath = commonPrefix . map (mapDEdge g) $ outdes
          -- Move the vertex's image forward along this common prefix path, and
          -- remove that common prefix from all outgoing directed edge images.
          newvmap = M.insert v (Maybe.fromJust $ pathEnd sg commonPath) vmap
          newemap = foldr adjustEdge emap outdes
          adjustEdge :: DEdge -> M.Map EdgeID Path -> M.Map EdgeID Path
          adjustEdge (DEdge e d) =
              case d of
                   Fwd  -> M.adjust (List.\\commonPath) e
                   Back -> M.adjust (reverse . (List.\\commonPath) . reverse) e

-- Pull the map tight. There's no kill like overkill.
pullTight :: GraphMap -> GraphMap
pullTight = deBacktrackAll . untilFixed deConstAll
    where deBacktrackAll (GraphMap sg vmap emap) =
              GraphMap sg vmap (M.map deBacktrack emap)
          deConstAll g@(GraphMap sg _ _) =
              foldl (flip deConstDerivative) g $ vertices sg

---------- 2.5 ----------

-- Fold the given collection of directed edges, all pointing out of the same
-- vertex and all mapping to the same edge-path which does not backtrack. If
-- the edges cannot be folded, error.
foldEdges :: [DEdge] -> GraphMap -> GraphMap
foldEdges [] g = assert False g
foldEdges (de:des) g@(GraphMap sg vmap emap) =
    assert (all (\de' -> mapDEdge g de' == mapDEdge g de) des) $
    GraphMap newsg newvmap newemap
    where newsg = foldl (flip $ flip foldEdge $ de) sg des
          newvmap = foldl (flip M.delete) vmap $
              map (snd . Maybe.fromJust . dirEndpoints sg) des
          newemap = foldl (flip M.delete) emap $
              map (\(DEdge e _) -> e) des

---------- 2.6 ----------

-- Subdivide the given edge by adding a vertex mapping to the given vertex on
-- the right. The edge must map to a path containing that vertex on the
-- interior, otherwise error.
-- TODO there is an issue determining what zone the added vertex lands in. Not
-- sure how to work this out yet, for now we just mush it (topologically) so
-- it's in the very first zone the edge passes through.
subdivide :: EdgeID -> VertexID -> GraphMap -> GraphMap
subdivide e v' g@(GraphMap sg@(SpineGraph vdata edata) vmap emap) =
    GraphMap (SpineGraph newvdata newedata) newvmap newemap
    where (p1,p2) = splitPath sg v' $ emap M.! e
          SpineEdge v1 v2 zs = edata M.! e
          v = newvid sg
          e1 = e
          e2 = neweid sg
          newedata = M.insert e1 (SpineEdge v1 v [head zs]) $
                     M.insert e2 (SpineEdge v v2 zs) $ edata
          newvdata = M.insert v (SpineVertex [e1,e2] [Back,Fwd] (head zs)) $
                     M.adjust fix v2 $ vdata
          fix :: SpineVertex -> SpineVertex
          fix (SpineVertex es ds z) = SpineVertex newes ds z
            where newes = map fst . replaceOne (e,Back) (e2,Back) $ zip es ds
          newvmap = M.insert v v' $ vmap
          newemap = M.insert e1 p1 $ M.insert e2 p2 $
            M.map (replaceAllL (DEdge e Fwd)
                               [(DEdge e1 Fwd),(DEdge e2 Fwd)]) $
            M.map (replaceAllL (DEdge e Back)
                               [(DEdge e2 Back),(DEdge e1 Back)]) $ emap


------ Helper functions for section 3 ------

-- Find all vertices of a given valence
verticesOfValence :: SpineGraph -> Int -> [VertexID]
verticesOfValence sg n = filter (\v -> valence sg v == n) $ vertices sg

-- Determines whether the invariant edges of the graph contain a cyclic path.
-- If so, return such a path. If not, return the invariant forest we built
-- up while "trying" to find a cycle.
findInvCycleOrForest :: GraphMap -> Either Path [Tree]
findInvCycleOrForest g@(GraphMap sg@(SpineGraph vdata edata) vmap emap) =
    fmap snd $
        -- We use foldM throughout so that if we find a cycle (the Left case)
        -- we will return it immediately without doing any more work.
        Monad.foldM (\(visitedivs,tmpforest) nextv ->
                      if elem nextv visitedivs
                         -- If already visited this vertex, skip it
                         then return (visitedivs,tmpforest)
                         -- Otherwise dfs it, and add the resulting list/tree
                         else do (vs, t) <- dfs nextv
                                 return (visitedivs ++ vs, tmpforest ++ [t]))
                    ([],[])
                    ivs
    where ivs = invariantVertices g
          -- Perform depth-first search starting at the given vertex, searching
          -- only invariant edges. Return either a cycle or a list of visited
          -- vertices together with a tree of vertices/edges built up.
          dfs :: VertexID -> Either Path ([VertexID], Tree)
          dfs v0 = fmap (mapFst M.keys) $
              -- As in dfsEdge, call recursively on all outgoing dedges and
              -- pass the visitmap along, now appending the trees to a list.
              Monad.foldM (\(tmpmap, tmplist) nextde ->
                            fmap (mapSnd $ (tmplist++) . (:[]))
                                 (dfsEdge nextde tmpmap))
                          (M.singleton v0 [], [])
                          outinvdes
            where -- All outgoing invariant edges of current vertex
                  SpineVertex es _ _ = vdata M.! v0
                  outinvdes = map (toOut sg v0) . filter (isInvariant g) $ es
          -- Perform depth-first search starting at the head of the given
          -- DEdge, searching only invariant edges and stopping at any vertex
          -- that's a key of the given dict of visited vertices. If we visit
          -- a vertex more than once, found a cycle.
          -- Return either the cycle containing an already-visited vertex (if
          -- we hit one) or a dict of visited vertices along with
          -- the tree of edges we built up (if not).
          -- Together with each visited vertex we store the path we took from
          -- our original starting vertex to that vertex. Each is "half" of the
          -- path/cycle we will return if we land on that vertex again.
          dfsEdge :: DEdge -> M.Map VertexID Path ->
              Either Path (M.Map VertexID Path, ETree)
          dfsEdge de@(DEdge e d) visitmap =
              if M.member v visitmap
                 -- If already visited, return the cycle, by combining the
                 -- existing paths to v0 (w/ edge e added) and to v
                 then Left $ newpath ++ revPath (visitmap M.! v)
                 -- Otherwise, mark as visited in new visit map, and call
                 -- recursively on all other outgoing dedges. Note that we
                 -- haven't traversed any of these edges yet (except the given
                 -- one) as otherwise we would already have visited vertex v.
                 -- For each outgoing edge call, we pass the visitmap along
                 -- through the fold, and insert the tree as a subtree of ours.
                 else Monad.foldM (\(tmpmap, tmptree) nextde ->
                                    fmap (mapSnd $ insertSubtree tmptree)
                                         (dfsEdge nextde tmpmap))
                                  (newvisitmap, (Graph.Node de []))
                                  outinvdes
            where (v0,v) = Maybe.fromJust $ dirEndpoints sg de
                  -- All outgoing invariant edges of current vertex
                  SpineVertex es _ _ = vdata M.! v
                  outinvdes = map (toOut sg v) . filter (isInvariant g) $
                      List.delete e es
                  -- Visit path of current vertex is visit path of previous
                  -- vertex (tail of edge e) together w given edge
                  newpath = ((visitmap M.! v0) ++ [de])
                  newvisitmap = M.insert v newpath visitmap

-- If such a forest was found, collapse it.
findAndCollapse :: GraphMap -> Either Path GraphMap
findAndCollapse g = Monad.liftM (flip collapseInvForest g) $
    findInvCycleOrForest g

-- Remove all vertices of valence one via isotopy.
removeAllValenceOne :: GraphMap -> GraphMap
removeAllValenceOne = untilFixed remove
    where remove g@(GraphMap sg _ _) =
              case verticesOfValence sg 1 of
                   []    -> g
                   (v:_) -> removeValenceOne v g

---------- 3.1 ----------

-- Given a graph map, determine the gates. To do this, observe
-- that in order for two elements of Lk(v) to be identified in the gate, their
-- images under (Dg)^n must be equal for some n. This can only occur if two
-- distinct elements of Lk(g^(n-1)(v)) are identified by Dg. Therefore we can
-- find all such identifications / equivalences by finding all locations where
-- Dg identifies two elements and taking repeated preimages.
--
-- We store the gate as a list of equivalence classes.
computeGates :: GraphMap -> M.Map VertexID [S.Set DEdge]
computeGates g@(GraphMap sg vmap _) = untilFixed doEqs initialGates
  where initialGates =
            M.fromList $ map (\v -> (v, map S.singleton $ outdes sg v)) $
                             vertices sg
        -- Combine any two gates whose representatives map to the same
        -- gate. We always reduce the number of sets, so this is guaranteed
        -- to terminate. This algo could be *much* more efficient.
        doEqs gates = M.mapWithKey doEqsOne gates
          where doEqsOne :: VertexID -> [S.Set DEdge] -> [S.Set DEdge]
                doEqsOne v = map S.unions . List.groupBy sameImage
                  where rhgate = gates M.! (vmap M.! v)
                        sameImage s1 s2 =
                          setFind rhgate (head $ mapDEdge g $ S.findMax s1) ==
                          setFind rhgate (head $ mapDEdge g $ S.findMax s2)

-- Determine whether the given graph map is efficient. If not, return the
-- offending edge (which maps to a backtracking edge under g^k, or equivalently
-- which passes through the same gate twice at a vertex.
-- findInefficient :: GraphMap -> Maybe DEdge

---------- 3.2 ----------

-- Construct a reduction or irreducible fibered surface carrying the given map.
-- We follow steps (1)-(4) in Bestvina-Handel exactly. TODO write a remotely
-- efficient version of this algorithm.
-- This function is quite confusingly written. Note that all the monadic
-- operators are just fancy function composition, and are used to allow the
-- "fail" case (Left Path) to fall through all other functions.
findReductionOrIrreducible :: GraphMap -> Either Path GraphMap
findReductionOrIrreducible =
    untilFixedM (
        untilFixedM (
            -- (1) Pull tight
            (return . pullTight) Monad.>=>
            -- (2) Collapse invariant forest
            findAndCollapse
        ) Monad.>=>
        -- (3) Remove all valence one vertices
        return . removeAllValenceOne
    )

-- Construct a reduction or an efficient fibered surface carrying the given
-- map.
findReductionOrEfficient :: GraphMap -> Either Path GraphMap

main :: IO ()
main = print "TODO XXX"
