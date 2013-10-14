module SurfaceGraph
( SurfaceGraph()
-- ID types are opaque
, Vertex(), Zone(), UEdge()
-- But edge directions can be extracted/used
, Dir(..)
, Edge(..)
, rev, revEdge
-- *Data needs to be visible in order to pattern match against
, VData(..)
, EData(..)
-- accessor functions for SurfaceGraph
, (!.), (!-), lookupV, lookupE
, vertices, uedges, newVertex, newUEdge, valence
-- mutator functions for SurfaceGraph
, collapseEdge, foldEdge
-- Paths
, Path, pathStart, pathEnd, revPath, splitPath, removeFromPath
) where

import qualified Data.List as List
import qualified Data.Map.Lazy as M
import Data.Map.Lazy ((!))
import Control.Exception.Base (assert)

import Util (commonPrefix)

-- A SurfaceGraph represents a graph which is embedded as the spine of a surface,
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
-- Note that all these types must be instances of Ord so they can be used as keys
-- in a Data.Map.Lazy.Map
newtype Vertex = Vertex { vertexId :: Int }
    deriving (Show,Eq,Ord)
newtype Zone   = Zone  Int -- { zoneId   :: Int }
    deriving (Show,Eq,Ord)


-- Internally we need to be able to identify edges independent of the direction we
-- traverse them, even though we primarily work with directed edges when
-- studying and manipulating the graph.
newtype UEdge  = UEdge  { uedgeId   :: Int }
    deriving (Show,Eq,Ord)
data Dir = Fwd | Back
    deriving (Show,Eq,Ord)
-- Directed edge = undirected edge + direction to traverse in
data Edge = Edge UEdge Dir
    deriving (Show,Eq,Ord)

rev :: Dir -> Dir
rev Fwd = Back
rev Back = Fwd

revEdge :: Edge -> Edge
revEdge (Edge ue d) = Edge ue (rev d)

-- Data associated with a vertex in the graph.
data VData = VData
    { incedges   :: [Edge] -- outgoing, in cyclic order in the embedded graph
    , zone       :: Zone
    } deriving (Show,Eq)
-- If an edge has both endpoints at a single vertex, the edge is listed twice
-- in the incident edge list (once Fwd and once Back)

-- Data associated with an edge in the spine graph.
data EData = EData
    { startvertex :: Vertex
    , endvertex   :: Vertex
    , zonepath    :: [Zone]
    } deriving (Show,Eq)

data SurfaceGraph = SurfaceGraph
    { vdata :: M.Map Vertex VData
    , edata :: M.Map UEdge EData
    -- Notice that we only store each edge's data once, not twice (once Fwd and
    -- once Back). By convention we store the data for the edge traversed in the
    -- Fwd direction.
    } deriving (Show,Eq)

-- Public accessors for a surface graph. Lookups return Nothing on
-- invalid Id, operator versions spit out error. How to remember:
-- (!.) because the dot looks like a vertex, (!-) the line looks like an edge.
lookupV :: SurfaceGraph -> Vertex -> Maybe VData
lookupV (SurfaceGraph vd _) v = M.lookup v vd
(!.) :: SurfaceGraph -> Vertex -> VData
(!.) (SurfaceGraph vd _) v = vd ! v

lookupE :: SurfaceGraph -> Edge -> Maybe EData
lookupE (SurfaceGraph _ ed) (Edge ue dir) = do
    EData v1 v2 zs <- M.lookup ue ed
    return $ case dir of
                  Fwd  -> EData v1 v2 zs
                  Back -> EData v2 v1 (reverse zs)
(!-) :: SurfaceGraph -> Edge -> EData
(!-) (SurfaceGraph _ ed) (Edge ue dir) =
    let EData v1 v2 zs = ed ! ue in
        case dir of
             Fwd  -> EData v1 v2 zs
             Back -> EData v2 v1 (reverse zs)

vertices :: SurfaceGraph -> [Vertex]
vertices = M.keys . vdata

uedges :: SurfaceGraph -> [UEdge]
uedges = M.keys . edata

-- Generate new Ids for vertices / edges to add to an existing graph.
newVertex :: SurfaceGraph -> Vertex
newVertex = Vertex . (+1) . vertexId . maximum . vertices

newUEdge :: SurfaceGraph -> UEdge
newUEdge = UEdge . (+1) . uedgeId . maximum . uedges

valence :: SurfaceGraph -> Vertex -> Int
valence sg v = List.length . incedges $ sg !. v

-- TODO To be used for testing
{-
isConsistent :: SurfaceGraph -> Bool
isConsistent (SurfaceGraph vd ed) = Maybe.isJust $ do
     Monad.forM_ (M.keys ed) checkEndpoints
     Monad.forM_ (M.keys vd) checkIncEdges
     where checkEndpoints :: UEdge -> Maybe ()
           checkEndpoints ue = do
               EData v1 v2 zs <- M.lookup ue ed
               -- Check that both endpoints of each (undirected) edge exist...
               VData _ z1 <- M.lookup v1 vd
               VData _ z2 <- M.lookup v2 vd
               -- ... and have the same zones as start/end zones of the edge
               ez1 <- Maybe.listToMaybe zs
               Monad.guard $ z1 == ez1 && z2 == last zs
           checkIncEdges :: Vertex -> Maybe ()
           checkIncEdges v = do
               VData ies _ <- M.lookup v vd
               Monad.forM_ ies checkIncEdge
               where checkIncEdge (Edge ue d) = do
                         -- Check that each incident edge exists...
                         EData v1 v2 _ <- M.lookup ue ed
                         -- ... and has that vertex as a start or end vertex
                         Monad.guard $ (v1 == v && d == Fwd) ||
                                       (v2 == v && d == Back)
-}

-- Represents a path of edges. For each edge we indicate whether we traverse it
-- forwards or backwards.
type Path = [Edge]

pathStart :: SurfaceGraph -> Path -> Maybe Vertex
pathStart _ [] = Nothing
pathStart sg p = Just $ startvertex $ sg !- head p

pathEnd :: SurfaceGraph -> Path -> Maybe Vertex
pathEnd _ [] = Nothing
pathEnd sg p = Just $ endvertex $ sg !- last p

revPath :: Path -> Path
revPath = reverse . map revEdge

-- Splits path at the first occurrence of the given vertex.
splitPath :: SurfaceGraph -> Vertex -> Path -> (Path,Path)
splitPath sg v = List.span ((/=v) . startvertex . (sg!-))

-- Removes all copies of the given edge, traversed in either direction, from
-- the given path.
removeFromPath :: Edge -> Path -> Path
removeFromPath (Edge ue _) = filter $ \(Edge ue' _) -> ue' /= ue

-- TODO To be used for testing
{-
isConsistentPath :: SurfaceGraph -> Path -> Bool
isConsistentPath _ [] = True
isConsistentPath sg p = Maybe.isJust $ Monad.zipWithM_ checkPair p (tail p)
    where checkPair e1 e2 = do
              -- end of each edge is start of the next
              EData _ v12 _ <- lookupE sg e1
              EData v21 _ _ <- lookupE sg e2
              Monad.guard $ v12 == v21
-}

-- Collapse the given edge in the graph. We collapse the edge (v1,v2) "fwd"
-- (that is, v1 is removed from the graph, and all edges incident to v1 are
-- pulled to be incident to v2, adjusting zones and cyclic orders
-- accordingly).
-- If v1 == v2, error.
collapseEdge :: Edge -> SurfaceGraph -> SurfaceGraph
collapseEdge e@(Edge ue _) sg@(SurfaceGraph vd ed) =
    assert (v1 /= v2) $
    SurfaceGraph newvd newed
    where EData v1 v2 zs  = sg !- e
          VData v1ies _   = sg !. v1
          VData v2ies v2z = sg !. v2
          -- Build new graph:
          -- 1. Modify the data of all edges incident to v1 to
          -- instead have v2 as a vertex, and modifying their zone lists
          -- accordingly. Also, remove the given edge.
          newed = foldl pulltov2 (M.delete ue ed) v1ies
          pulltov2 tmped e'@(Edge ue' d') =
              case d' of
                   Back ->
                       -- v1 was the 2nd vertex of edge e'
                       M.insert ue' (EData v1' v2 $ zs'++zs) tmped
                   Fwd  ->
                       -- v1 was the 1st vertex of edge e'
                       M.insert ue' (EData v2 v2' $ (reverse zs)++zs') tmped
              where EData v1' v2' zs' = sg !- e'
          -- 2. Modify incidence list at v2 to include pulled edges, inserting
          -- them at the location of the collapsed edge in the cyclic order.
          -- Also, remove v1 from vertices
          newvd = M.insert v2 (VData newies v2z) $
              M.delete v1 vd
              where ix1 = maybe (error "Inconsistent graph") id $
                            List.elemIndex e v1ies
                    ix2 = maybe (error "Inconsistent graph") id $
                            List.elemIndex (revEdge e) v2ies
                    -- The incident edge at v1 "after" (v1,v2) in cyclic order
                    -- is pulled to immediately "after"
                    -- the incident edge at v2 "before" (v1,v2)
                    -- (Draw a picture, it makes sense)
                    newies = (take ix2 v2ies) ++
                             (drop (ix1+1) v1ies) ++
                             (take ix1 v1ies) ++
                             (drop (ix2+1) v2ies)

-- Folds the (1st) given edge (v0,v1) in the graph onto the (2nd) given edge
-- (v0,v2) in the graph. Both edges must have the same starting vertex and
-- adjacent ending vertices in the cyclic order around the start vertex.
foldEdge :: Edge -> Edge -> SurfaceGraph -> SurfaceGraph
foldEdge e1@(Edge ue1 _) e2 sg@(SurfaceGraph vd ed) =
        assert (v0 == v0') $
        assert (List.isInfixOf [e1,e2] v0ies || List.isInfixOf [e2,e1] v0ies) $
        SurfaceGraph newvd newed
    where EData v0  v1 zs1 = sg !- e1
          EData v0' v2 zs2 = sg !- e2
          VData v0ies _    = sg !. v0
          VData v1ies _    = sg !. v1
          VData v2ies v2z  = sg !. v2
          -- Build new graph:
          -- 1. Modify the data of all edges incident to v1 to
          -- instead have v2 as a vertex, and modifying their zone lists
          -- accordingly. In order to fold the edges together, each edge
          -- formerly incident to v1 must traverse all zones traversed by
          -- (v0,v1) edge (in reverse order) followed by zones traversed by
          -- (v0,v2) edge - except for zones shared by both these edges. Also,
          -- remove (v0,v1) edge.
          commonzs = commonPrefix [zs1,zs2]
          newzs = (reverse $ zs1 List.\\ commonzs) ++ (zs2 List.\\ commonzs)
          newed = foldl movetov2 (M.delete ue1 ed) v1ies
          movetov2 tmped e'@(Edge ue' d') =
            case d' of
                 Back ->
                   -- v1 was the 2nd vertex of edge e'
                   M.insert ue' (EData ev1 v2 $ ezs++newzs) tmped
                 Fwd  ->
                   -- v1 was the 1st vertex of edge e'
                   M.insert ue' (EData v2 ev2 $ (reverse newzs)++ezs) tmped
            where EData ev1 ev2 ezs = sg !- e'
          -- 2. Modify incidence list at v2 to include moved edges, inserting
          -- them above/below the location of the edge (v0,v2) in the cyclic
          -- order (depending on whether the edge (v0,v1) lies above or below
          -- the edge (v0,v2))
          -- Also, remove v1 from vertices.
          newvd = M.insert v2 (VData newies v2z) $
              M.delete v1 vd
              where ix1 = maybe (error "Inconsistent graph") id $
                            List.elemIndex (revEdge e1) v1ies
                    ix2 = maybe (error "Inconsistent graph") id $
                            List.elemIndex (revEdge e2) v2ies
                    -- The incident edge at v1 "after" (v0,v1) in cyclic order
                    -- becomes "first" among all edges moved to v2. All edges
                    -- moved from v1 come (in a clump) after (v0,v2) if pushed
                    -- from below and before if pushed from above.
                    newies = if List.isInfixOf [e1,e2] v0ies
                                then (take ix2 v2ies) ++
                                     (drop (ix1+1) v1ies) ++
                                     (take ix1 v1ies) ++
                                     (drop ix2 v2ies)
                                else (take (ix2-1) v2ies) ++
                                     (drop (ix1+1) v1ies) ++
                                     (take ix1 v1ies) ++
                                     (drop (ix2-1) v2ies)
