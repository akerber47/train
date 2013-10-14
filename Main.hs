import qualified Data.List as List
import Data.List((\\))
import qualified Data.Map.Lazy as M
import Data.Map.Lazy ((!))
import qualified Data.Set as S
import qualified Data.Maybe as Maybe
import qualified Control.Monad as Monad
import qualified Data.Graph as Graph

import Control.Exception.Base (assert)
import Data.Functor ((<$>))

import Util (untilFixed, untilFixedM, commonPrefix, mapFst, mapSnd)
import qualified SurfaceGraph as SG
import SurfaceGraph ((!.), (!-))

-- Returns the maximum member of the (first) set in the given list of sets
-- which contains the given element. Because I am too lazy to implement
-- union-find properly.
setFind :: (Ord a) => [S.Set a] -> a -> a
setFind sets x = S.findMax . head . filter (S.member x) $ sets

-- Map sends vertices to vertices, and edges to edge paths. By convention each
-- edge is oriented in the fwd direction (1st vertex to 2nd vertex) when
-- describing the map of edges to (oriented) edge paths.
data GraphMap = GraphMap
    { graph :: SG.SurfaceGraph
    , vmap  :: M.Map SG.Vertex SG.Vertex
    , emap  :: M.Map SG.UEdge SG.Path
    } deriving (Show,Eq)

-- Similarly to the surface graph accessors. Think "apply to vertex" and "apply
-- to edge"

mapV :: GraphMap -> SG.Vertex -> Maybe SG.Vertex
mapV (GraphMap _ vm _) v = M.lookup v vm

($.) :: GraphMap -> SG.Vertex -> SG.Vertex
($.) (GraphMap _ vm _) v = vm ! v

mapE :: GraphMap -> SG.Edge -> Maybe SG.Path
mapE (GraphMap _ _ em) (SG.Edge ue d) =
    case d of SG.Fwd  -> M.lookup ue em
              SG.Back -> SG.revPath <$> M.lookup ue em

($-) :: GraphMap -> SG.Edge -> SG.Path
($-) (GraphMap _ _ em) (SG.Edge ue d) =
    case d of SG.Fwd  -> em ! ue
              SG.Back -> SG.revPath $ em ! ue

vertexPreimage :: GraphMap -> SG.Vertex -> [SG.Vertex]
vertexPreimage (GraphMap _ vm _) v = M.keys $ M.filter (== v) vm

-- Will be used for testing
{-
isConsistentMap :: GraphMap -> Bool
isConsistentMap (GraphMap sg vm em) =
    -- Maps are defined for all vertices / edges
    S.fromList (SG.vertices sg) == M.keysSet vm &&
    S.fromList (SG.uedges   sg) == M.keysSet em &&
    (Maybe.isJust $ do
        -- Each vertex maps to a well-defined vertex
        Monad.forM_ (M.elems vm) (SG.lookupV sg)
        -- Each edge maps to a well-defined consistent edge path
        Monad.forM_ (M.keys em) checkEdge)
    where checkEdge ue = do
            (SG.SG.EData v1 v2 _) <- SG.lookupE sg (SG.Edge ue SG.Fwd)
            gv1 <- M.lookup v1 vm
            gv2 <- M.lookup v2 vm
            path <- M.lookup ue em
            case path of
                 -- Empty path stays at a single vertex
                 [] -> Monad.guard $ gv1 == gv2
                 p  -> do
                     -- Nonempty path has correct endpoints
                     p1 <- SG.pathStart sg path
                     p2 <- SG.pathEnd sg path
                     Monad.guard $ gv1 == p1 && gv2 == p2
            -- Interior edges of path line up consistently
            Monad.guard $ isConsistentPath sg path
-}

-- Derivative of map at given oriented edge, as in Bestvina-Handel.
-- Nothing if edge collapses.
derivative :: GraphMap -> SG.Edge -> Maybe SG.Edge
derivative g = Maybe.listToMaybe . (g$-)

-- Inverse image of derivative at given oriented edge (and given preimage
-- vertex). Error if given vertex is not preimage of given edge's 1st vertex.
derivativePreimage :: GraphMap -> SG.Vertex -> SG.Edge -> [SG.Edge]
derivativePreimage g@(GraphMap sg _ _) v e =
    assert (elem v $ vertexPreimage g v1) $
        filter ((==(Just e)) . derivative g) . SG.incedges $ sg !. v
    where v1 = SG.startvertex $ sg !- e

-- All possible derivative preimages at given oriented edge.
fullDerivativePreimage :: GraphMap -> SG.Edge -> [(SG.Vertex, [SG.Edge])]
fullDerivativePreimage g@(GraphMap sg _ _) e =
    map (\v -> (v,derivativePreimage g v e)) vs
    where vs = vertexPreimage g . SG.startvertex $ sg !- e

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
isoVertex :: SG.Edge -> SG.Vertex -> GraphMap -> GraphMap
isoVertex e@(SG.Edge ue d) v g@(GraphMap sg vm em)
    = GraphMap sg newvm newem
    where SG.VData ies _   = sg !. v
          SG.EData v1 v2 _ = sg !- e
          -- Vertex (which mapped to v1) now maps to v2
          newvm = assert (v1 == (g $. v)) $
              M.insert v v2 vm
          -- Each incident edge maps to a path with one additional step
          -- If the uedge goes out of v, we add (v2,v1) to the front
          -- if into v, we add (v1,v2) to the back.
          newem = foldl adj em ies
          adj :: M.Map SG.UEdge SG.Path -> SG.Edge -> M.Map SG.UEdge SG.Path
          adj em' e'@(SG.Edge ue' d') =
              case d' of SG.Fwd  -> M.adjust ([SG.revEdge e'] ++) ue' em'
                         SG.Back -> M.adjust (++ [e']) ue' em'

-- Isotope the given map by postcomposing with an isotopy "pulling the given
-- edge's start vertex across itself". That is, apply the earlier isotopy to
-- all preimages of the given edge's starting vertex.
--
-- Similarly, error if edge not present.
isoVertexOnRight :: SG.Edge -> GraphMap -> GraphMap
isoVertexOnRight e g@(GraphMap sg _ _) =
    foldr (isoVertex e) g (vertexPreimage g . SG.startvertex $ sg !- e)

-- Isotope the given map so that all preimages of the given edge's starting
-- vertex are pulled across the given edge. Then collapse the given edge,
-- removing it and its 1st vertex from both graph and map.
isoAndCollapse :: SG.Edge -> GraphMap -> GraphMap
isoAndCollapse e@(SG.Edge ue _) g@(GraphMap sg _ _) =
    GraphMap newsg newvm newem
    where -- Remove the offending edge from the graph itself
          newsg = SG.collapseEdge e sg
          -- Postcompose g with isotopy so that no vertex lands on 1st vertex.
          -- We can safely remove all copies of the given edge
          -- from paths edges map to (as the new paths will be isotopic to old)
          -- Also we remove this edge and vertex from the map.
          SG.EData v1 v2 _ = sg !- e
          GraphMap _ vm em = isoVertexOnRight e g
          newvm = M.delete v1 vm
          newem = M.map (SG.removeFromPath e) $ M.delete ue em


-- Check whether vertices/edges which are fixed under the given map.
isInvV :: GraphMap -> SG.Vertex -> Bool
isInvV g v = v == g $. v
isInvE :: GraphMap -> SG.Edge -> Bool
isInvE g e = [e] == g $- e

------------------------------------------------------------------------------
------------------------------------------------------------------------------
------------------------------------------------------------------------------

-- Implementations of the fibered surface moves.

---------- 2.1 ----------

-- Collapse an edge which is invariant under the given map. If edge is not
-- invariant, error. Also cannot collapse loop edge.
collapseInvEdge :: SG.Edge -> GraphMap -> GraphMap
collapseInvEdge e g@(GraphMap sg _ _) =
    assert (isInvE g e && v1 /= v2) $ isoAndCollapse e g
    where SG.EData v1 v2 _ = sg !- e

-- Insert given tree (2nd arg) in as child of given node of another tree (1st)
-- inserts after all other children of that node.
insertSubtree :: Graph.Tree a -> Graph.Tree a -> Graph.Tree a
insertSubtree (Graph.Node x ts) t = Graph.Node x (ts ++ [t])

-- Represents a tree of vertices/edges in a SG.SurfaceGraph. All edges point "down".
-- This needs to be a list of trees bc there may be multiple edges out of
-- root vertex - these will be the "root edges"
type Tree = [Graph.Tree SG.Edge]

-- Represents a tree of edges in a SG.SurfaceGraph. All edges point "down". This has
-- a "root edge" rather than a root vertex
type ETree = Graph.Tree SG.Edge


-- Collapse an entire forest of invariant vertices/edges. If forest is not
-- invariant, error.
collapseInvForest :: [Tree] -> GraphMap -> GraphMap
-- Note that a list of Trees is a list of lists of ETrees
collapseInvForest ts g = foldl (foldl collapseETree) g ts
    where collapseETree :: GraphMap -> ETree -> GraphMap
          -- Collapse outermost edges first, finishing with root edge.
          -- Edges in an ETree point outward, so need to reverse them.
          collapseETree tmpg (Graph.Node de ets) =
              collapseInvEdge (SG.revEdge de) $ foldl collapseETree tmpg ets

---------- 2.2 ----------

-- Remove a valence 1 vertex via isotopy. If the vertex is not valence 1, error
removeValenceOne :: SG.Vertex -> GraphMap -> GraphMap
removeValenceOne v g@(GraphMap sg _ _) =
    assert (SG.valence sg v == 1) $
        isoAndCollapse (head ies) g
    where SG.VData ies _ = sg !. v

---------- 2.3 ----------

-- Remove a valence 2 vertex via isotopy. If the vertex is not valence 2, error
removeValenceTwo :: SG.Vertex -> GraphMap -> GraphMap
removeValenceTwo v g@(GraphMap sg _ _) =
    assert (SG.valence sg v == 2) $
        -- Find first outgoing edge, then collapse it
        -- (this will automatically pull 2nd edge "across the bridge")
        isoAndCollapse (head ies) g
    where SG.VData ies _ = sg !. v


---------- 2.4 ----------

-- Two functions to pull the map tight.

-- Return a path which does not backtrack, by removing all parts of the path
-- which double back on themselves.
-- This algorithm is grotesquely inefficient.
deBacktrack :: SG.Path -> SG.Path
deBacktrack = untilFixed deBacktrackPair
    where -- Remove the first matching backtracking pair of path components,
          -- e.g. given path (e1 Fwd),(e1 Back),(e2 Back),(e2 Fwd),(e2 Back),
          -- the first two path components will be removed.
          deBacktrackPair :: SG.Path -> SG.Path
          deBacktrackPair [] = []
          deBacktrackPair [e] = [e]
          deBacktrackPair (e1:e2:es)
            | e1 == SG.revEdge e2 = es
            | otherwise           = e1:e2:(deBacktrackPair es)

-- Modify the map by isotopy so that derivative will not be constant at given
-- vertex (once paths are pulled tight / deBacktracked), by pulling its image
-- forward along the edge which is image of derivative.
deConstDerivative :: SG.Vertex -> GraphMap -> GraphMap
deConstDerivative v g@(GraphMap sg vm em)
    | commonp == [] = g
    | otherwise     = GraphMap sg newvm newem
    where SG.VData ies _ = sg !. v
          commonp = commonPrefix $ map (g$-) ies
          -- Move the vertex's image forward along this common prefix path, and
          -- remove that common prefix from all outgoing directed edge images.
          newvm = M.insert v (Maybe.fromJust $ SG.pathEnd sg commonp) vm
          newem = foldl adj em ies
          adj :: M.Map SG.UEdge SG.Path -> SG.Edge -> M.Map SG.UEdge SG.Path
          adj em' e@(SG.Edge ue d) =
              case d of
                   SG.Fwd  -> M.adjust (\\commonp) ue em'
                   SG.Back -> M.adjust (reverse . (\\commonp) . reverse) ue em'

-- Pull the map tight. There's no kill like overkill.
pullTight :: GraphMap -> GraphMap
pullTight = deBacktrackAll . untilFixed deConstAll
    where deBacktrackAll (GraphMap sg vm em) =
              GraphMap sg vm (M.map deBacktrack em)
          deConstAll g@(GraphMap sg _ _) =
              foldl (flip deConstDerivative) g $ SG.vertices sg

---------- 2.5 ----------

-- Fold the given collection of directed edges, all pointing out of the same
-- vertex and all mapping to the same edge-path which does not backtrack. If
-- the edges cannot be folded, error.
foldEdges :: [SG.Edge] -> GraphMap -> GraphMap
foldEdges [] g = assert False g
foldEdges (e:es) g@(GraphMap sg vm em) =
    assert (all (\e' -> g $- e' == g $- e) es) $
    GraphMap newsg newvm newem
    where newsg = foldl (flip $ flip SG.foldEdge $ e) sg es
          newvm = foldl (flip M.delete) vm $
              map (SG.endvertex . (sg!-)) es
          newem = foldl (flip M.delete) em $
              map (\(SG.Edge e' _) -> e') es

---------- 2.6 ----------

-- TODO fix this, requires digging into surface graph again.
{-
-- Subdivide the given edge by adding a vertex mapping to the given vertex on
-- the right. The edge must map to a path containing that vertex on the
-- interior, otherwise error.
-- TODO there is an issue determining what zone the added vertex lands in. Not
-- sure how to work this out yet, for now we just mush it (topologically) so
-- it's in the very first zone the edge passes through.
subdivide :: SG.UEdge -> SG.Vertex -> GraphMap -> GraphMap
subdivide e v' g@(GraphMap sg@(SG.SurfaceGraph vd ed) vm em) =
    GraphMap (SG.SurfaceGraph newvd newed) newvm newem
    where (p1,p2) = splitPath sg v' $ em ! e
          SG.EData v1 v2 zs = ed ! e
          v = newvid sg
          e1 = e
          e2 = neweid sg
          newed = M.insert e1 (SG.EData v1 v [head zs]) $
                     M.insert e2 (SG.EData v v2 zs) $ ed
          newvd = M.insert v (SG.VData [e1,e2] [Back,Fwd] (head zs)) $
                     M.adjust fix v2 $ vd
          fix :: SG.VData -> SG.VData
          fix (SG.VData es ds z) = SG.VData newes ds z
            where newes = map fst . replaceOne (e,Back) (e2,Back) $ zip es ds
          newvm = M.insert v v' $ vm
          newem = M.insert e1 p1 $ M.insert e2 p2 $
            M.map (replaceAllL (SG.Edge e Fwd)
                               [(SG.Edge e1 Fwd),(SG.Edge e2 Fwd)]) $
            M.map (replaceAllL (SG.Edge e Back)
                               [(SG.Edge e2 Back),(SG.Edge e1 Back)]) $ em
-}

------ Helper functions for section 3 ------

-- Find all vertices of a given valence
verticesOfValence :: SG.SurfaceGraph -> Int -> [SG.Vertex]
verticesOfValence sg n = filter (\v -> SG.valence sg v == n) $ SG.vertices sg

-- Determines whether the invariant edges of the graph contain a cyclic path.
-- If so, return such a path. If not, return the invariant forest we built
-- up while "trying" to find a cycle.
findInvCycleOrForest :: GraphMap -> Either SG.Path [Tree]
findInvCycleOrForest g@(GraphMap sg vm em) =
    -- We use foldM throughout so that if we find a cycle (the Left case)
    -- we will return it immediately without doing any more work.
    snd <$> Monad.foldM
        (\(visitedvs,tmpforest) nextv ->
            if elem nextv visitedvs
               -- If already visited this vertex, skip it
               then return (visitedvs,tmpforest)
               -- Otherwise dfs it, and add the resulting
               -- list/tree to accumulators
               else do (vs', t') <- dfs nextv
                       return (visitedvs ++ vs', tmpforest ++ [t']))
        ([],[])
        vs
    where vs = filter (isInvV g) $ SG.vertices sg
          -- Perform depth-first search starting at the given vertex, searching
          -- only invariant edges. Return either a cycle or a list of visited
          -- vertices together with a tree of vertices/edges built up.
          dfs :: SG.Vertex -> Either SG.Path ([SG.Vertex], Tree)
          dfs v0 = mapFst M.keys <$>
              -- As in dfsEdge, call recursively on all outgoing dedges and
              -- pass the visitmap along, now appending the trees to a list.
              Monad.foldM (\(tmpmap, tmplist) nextde ->
                            fmap (mapSnd $ (tmplist++) . (:[]))
                                 (dfsEdge nextde tmpmap))
                          (M.singleton v0 [], [])
                          (filter (isInvE g) ies)
            where -- All outgoing invariant edges of current vertex
                  SG.VData ies _ = sg !. v0
          -- Perform depth-first search starting at the head of the given
          -- SG.Edge, searching only invariant edges and stopping at any vertex
          -- that's a key of the given dict of visited vertices. If we visit
          -- a vertex more than once, found a cycle.
          -- Return either the cycle containing an already-visited vertex (if
          -- we hit one) or a dict of visited vertices along with
          -- the tree of edges we built up (if not).
          -- Together with each visited vertex we store the path we took from
          -- our original starting vertex to that vertex. Each is "half" of the
          -- path/cycle we will return if we land on that vertex again.
          dfsEdge :: SG.Edge -> M.Map SG.Vertex SG.Path ->
              Either SG.Path (M.Map SG.Vertex SG.Path, ETree)
          dfsEdge e@(SG.Edge ue _) visitmap =
              if M.member v visitmap
                 -- If already visited, return the cycle, by combining the
                 -- existing paths to v0 (w/ edge e added) and to v
                 then Left $ newpath ++ SG.revPath (visitmap ! v)
                 -- Otherwise, mark as visited in new visit map, and call
                 -- recursively on all other outgoing dedges. Note that we
                 -- haven't traversed any of these edges yet (except the given
                 -- one) as otherwise we would already have visited vertex v.
                 -- For each outgoing edge call, we pass the visitmap along
                 -- through the fold, and insert the tree as a subtree of ours.
                 else Monad.foldM (\(tmpmap, tmptree) nexte ->
                                    mapSnd (insertSubtree tmptree) <$>
                                        dfsEdge nexte tmpmap)
                                  (newvisitmap, (Graph.Node e []))
                                  (filter (isInvE g) $ List.delete e ies)
              where SG.EData v0 v _ = sg !- e
                    -- All outgoing invariant edges of current vertex
                    SG.VData ies _ = sg !. v
                    -- Visit path of current vertex is visit path of previous
                    -- vertex (tail of edge e) together w given edge
                    newpath = ((visitmap ! v0) ++ [e])
                    newvisitmap = M.insert v newpath visitmap

-- If such a forest was found, collapse it.
findAndCollapse :: GraphMap -> Either SG.Path GraphMap
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
computeGates :: GraphMap -> M.Map SG.Vertex [S.Set SG.Edge]
computeGates g@(GraphMap sg vm _) = untilFixed doEqs initialGates
  where initialGates =
            M.fromList $
                map (\v -> (v, map S.singleton . SG.incedges $ sg !. v)) $
                    SG.vertices sg
        -- Combine any two gates whose representatives map to the same
        -- gate. We always reduce the number of sets, so this is guaranteed
        -- to terminate. This algo could be *much* more efficient.
        doEqs gates = M.mapWithKey doEqsOne gates
          where doEqsOne :: SG.Vertex -> [S.Set SG.Edge] -> [S.Set SG.Edge]
                doEqsOne v = map S.unions . List.groupBy sameImage
                  where rhgate = gates ! (vm ! v)
                        sameImage s1 s2 =
                          setFind rhgate (head $ g $- S.findMax s1) ==
                          setFind rhgate (head $ g $- S.findMax s2)

-- Determine whether the given graph map is efficient. If not, return the
-- offending edge (which maps to a backtracking edge under g^k, or equivalently
-- which passes through the same gate twice at a vertex.
-- findInefficient :: GraphMap -> Maybe SG.Edge

---------- 3.2 ----------

-- Construct a reduction or irreducible fibered surface carrying the given map.
-- We follow steps (1)-(4) in Bestvina-Handel exactly. TODO write a remotely
-- efficient version of this algorithm.
-- This function is quite confusingly written. Note that all the monadic
-- operators are just fancy function composition, and are used to allow the
-- "fail" case (Left SG.Path) to fall through all other functions.
findReductionOrIrreducible :: GraphMap -> Either SG.Path GraphMap
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
-- findReductionOrEfficient :: GraphMap -> Either SG.Path GraphMap

main :: IO ()
main = print "TODO XXX"
