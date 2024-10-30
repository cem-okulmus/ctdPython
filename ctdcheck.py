import networkx as nx

from hypergraph import HyperGraph

class VertSet(object):
    def __init__(self,vertices):
        assert(type(vertices) == set)
        self.vertices = vertices
         
    def __hash__(self):
        finalHash = 0 
        for h in self.vertices:
            finalHash = finalHash + hash(h)
        return finalHash   
        
    def __repr__(self):        
        return str(self.vertices)

    def __eq__(self, other):
        return type(other) == VertSet and self.vertices == other.vertices

class Block(object):
    def __init__(self,head,cover,tail):
        assert(type(head) == VertSet)
        assert(type(tail) == VertSet)
        assert(len(head.vertices.intersection(tail.vertices)) == 0) # disjoint
        self.head = head
        self.cover = cover
        self.tail = tail

    def __hash__(self):
        finalHash = 0 
        for h in self.head.vertices:
            finalHash = finalHash + hash(h)
        for t in self.tail.vertices:
            finalHash = finalHash + hash(t)
        return finalHash

    def __eq__(self, other):
        return type(other) == Block and self.head == other.head and self.tail == other.tail
            
    def __repr__(self):
        return "("+str(self.head)+","+str(self.tail)+")"


    def __lt__(self,other):
        selfVert = self.head.vertices.union(self.tail.vertices) 
        otherVert = other.head.vertices.union(other.tail.vertices) 

        return selfVert.issubset(otherVert) and self.tail.vertices.issubset(other.tail.vertices)

    # connected bags filters out any bags for which the induced subgraph over E is not connected
    def connected(self):
        coverGraph = HyperGraph()

        for e in self.cover: 
            coverGraph.add_edge(e.V,e.name)
        comps = coverGraph.separate(set())
        # if len(comps) == 1: 
        #     print("For the block " + str(self)  + " with cover "+ str(self.cover)+ " there are these components " + str(comps) )
      
        return len(comps) == 1 # connected if only one connected comp



class Node:
    def __init__(self,bag,cover,children):
        assert(type(bag) == VertSet)
        self.bag = bag  # set of vertices
        self.cover = cover #set of edges
        self.children = children #set of child nodes

    def addChild(self,child):
        self.children.append(child)

    def getGraphRoot(self,vertex):
        return self.getGraph(vertex,"0") #not sure if this derefecne works

    def getGraph(self,vertex,prefix): 
        G = nx.Graph() 

        # add new edges
        if (vertex in self.bag.vertices):
            G.add_node(prefix)
            for i, c in enumerate(self.children): 
                if (vertex in c.bag.vertices):
                    nodeName = prefix + str(i)
                    G.add_edge(prefix,nodeName)

        #collect edges from children
        for i, c in enumerate(self.children): 
            subG = c.getGraph(vertex,prefix + str(i))
            for (s,e) in subG.edges:
                G.add_edge(s,e)

        return G

    def coverCheck(self):
        verticesCover = set()

        for e in self.cover:
            for v in e.V:
                verticesCover.add(v)

        if not(self.bag.vertices <= verticesCover):
            print(" bag "  + str(self.bag)  + " not covered by cover " + str(self.cover))

            print(" bag "  + str(self.bag.vertices)  )
            print(" cover "  + str(verticesCover)  )
            return False

        for c in self.children: 
            if not(c.coverCheck()):
                return False

        return True


    def edgeCovered(self,e):
        if (e.V <= self.bag.vertices):
            return True
        for c in self.children:
            if c.edgeCovered(e):
                return True
       
        return False

    def allEdgesCovered(self,H):
        result = True 
        for e in H.E:
            if not(self.edgeCovered(e)):
                print("The edge " + str(e) + " is not covered!")
                result = False

        return result

    def isConnected(self,H):
        result = True

        for n in H.V:
            subG = self.getGraphRoot(n)
            comps = nx.connected_components(subG)
            if len(list(comps)) > 1:
                print("subtree on vertex " + str(n)  + " is not connected")
                print("comps: ", list(comps))
                result = False

        return result


    def isCorrect(self,H):
        return self.isConnected(H) and self.allEdgesCovered(H) and self.coverCheck()


    def toString(self,depth):

        tabby = "\n " + "\t" * depth
        

        childrenReps = list()
        for child in self.children:
            childrenReps.append(child.toString(depth+1))

        return "Bag: " + str(self.bag) + " Cover: " + str(self.cover) + tabby + tabby.join(childrenReps)

    def __repr__(self):        
        return self.toString(1)




class CTDCheck(object):
    def __init__(self,h):
        self.H = h                   # hypergraph
        self.blocks = set()
        self.satisfied_block = set() # indicating which blocks are satisfied
        self.head_to_blocks = dict() # mapping heads to blocks headed by them
        self.block_to_basis = dict() # mapping a satisfied block to its basis
        self.rootHead = None # cache the root head once found
        self.head_to_cover = dict() # cache the edge covers

    def addBlock(self,b):
        assert(type(b) == Block)
        if b in self.blocks:
            return # don't add same block twice
        self.blocks.add(b)
        self.head_to_cover[b.head] = b.cover
        # print("Is the head ", b.head ," hash:",hash(b.head)  ," already in the map ", list(self.head_to_blocks.keys()))
        # print("Answer: ", b.head in list(self.head_to_blocks.keys()))
        if b.head in self.head_to_blocks:
            self.head_to_blocks[b.head].append(b)
        else:
            self.head_to_blocks[b.head] = [b]            
        
        if len(b.tail.vertices) == 0: 
            # print("Block ",b," added as trivially sat.")
            self.satisfied_block.add(b)  # check if trivially satisifed
        # else:
        #     self.block_dict[b] = self.hasBasis(b) # basis check


    # this function is deliberately not recursive, to keep things simple
    # in other words, it needs to be called repeatedly, in a "top down" fashion
    def hasBasis(self,b):
        basisFound = False
        basisWitness = None
        for B in self.head_to_blocks:
            allBlocks = self.head_to_blocks[B]
            blocks = [x for x in allBlocks if x < b]

            cond3 = True
            for ob in blocks:
                if not ob in self.satisfied_block:
                    cond3 = False
            if cond3 == False:
                continue #3nd Condition violated (testing first for efficiency)

            unionTails = set()
            for ob in blocks:
                for v in ob.tail.vertices:
                    unionTails.add(v)
            for v in B.vertices:
                unionTails.add(v)
            if not  b.tail.vertices.issubset(unionTails):
                continue # 1st Condition violated
            cond2 = True
            for e in self.H.E:
                if len(e.V.intersection(b.tail.vertices)) == 0:
                    continue # find other edge
                if not e.V.issubset(unionTails):
                    cond2 = False
                    break
            if cond2 == False:
                continue # 2nd Condition vioalted
            basisFound = True
            basisWitness = B
            # print("The basis of ", b , " is ", B)
            # print("The blocks headed by ", B)
            # for BB in blocks:
            #     print(str(BB)+"\n")

            break
        if basisFound == True:
            self.satisfied_block.add(b)
            self.block_to_basis[b] = basisWitness
            return True
        else:
            return False

    def rootHeadFound(self):
        for head in self.head_to_blocks:
            blocks = self.head_to_blocks[head]
            allSatisfied = True
            for b in blocks:
                if not b in self.satisfied_block:
                    allSatisfied = False
            if allSatisfied == True:
                # print("Root Head is ",head)
                self.rootHead = head
                return True
        return False


    def hasDecomp(self):
        while True:            
            changed = False
            for b in self.blocks:
                if b in self.satisfied_block:
                    continue # already marked as satisfied
                res = self.hasBasis(b)
                if res == True:
                    changed = True
                    # print("Found basis for the block ", b)
                if self.rootHeadFound():
                    # print("Found decomp!")
                    return True
            if changed == False:
                # print("Nothing has changed anymore, terminating")
                return False

    def getDecomp(self,block):
        if not(block in self.satisfied_block):
            # print(block, " is not satisfied")
            return None  # Nothing to return if block not satisfied
        if len(block.tail.vertices) == 0:
            # print(block, " is trivial")
            return Node(block.head,self.head_to_cover[block.head],list()) # leaf node
        basis = self.block_to_basis[block]
        allBlocks = self.head_to_blocks[basis]
        blocks = [x for x in allBlocks if x < block and len(x.tail.vertices) != 0]

        # print("Child BLocks for block ", block)
        # for bs in allBlocks:
        #     print(bs)

        children = list()
        for bs in blocks: 
            children.append(self.getDecomp(bs))
        
        return Node(basis,self.head_to_cover[basis],children)


    def getDecompRoot(self):
        if self.rootHead == None:
            return None  ## can't find decomp of whole graph if no root head

        allBlocks = self.head_to_blocks[self.rootHead]
        # print("Blocks of RootHead")
        # for bs in allBlocks:
        #     print(bs)


        blocks = [x for x in allBlocks if len(x.tail.vertices) != 0]

        # print("Non-Trivial Blocks of RootHead")
        # for bs in blocks:
        #     print(bs)

        children = list()
        for bs in blocks:
            children.append(self.getDecomp(bs))

        return Node(self.rootHead,self.head_to_cover[self.rootHead],children)






class CTDOpt(object):
    def __init__(self,h):
        self.H = h                   # hypergraph
        self.root_block = Block(VertSet(set()), set(), VertSet(h.V))
        self.blocks = set([self.root_block])
        self.satisfied_block = set() # indicating which blocks are satisfied
        self.head_to_blocks = dict() # mapping heads to blocks headed by them
        self.weights = dict() # maps block to weight
        self.weights[self.root_block] = sys.maxsize
        self.sj_weights = dict()
        self.children = dict()
        self.top_children = dict()
        self.top_children[self.root_block] = []
        self.new_blocks = set()
        self.head_to_cover = dict() # cache the edge covers
        self.block_to_basis = dict() # mapping a satisfied block to its basis
        self.rootHead = None # cache the root head once found

    def addBlock(self,b):
        assert(type(b) == Block)
        if b in self.blocks:
            return # don't add same block twice
        self.blocks.add(b)
        self.head_to_cover[b.head] = b.cover
        self.new_blocks.add(b)
        # print("Is the head ", b.head ," hash:",hash(b.head)  ," already in the map ", list(self.head_to_blocks.keys()))
        # print("Answer: ", b.head in list(self.head_to_blocks.keys()))
        if b.head in self.head_to_blocks:
            self.head_to_blocks[b.head].append(b)
        else:
            self.head_to_blocks[b.head] = [b]            

        self.top_children[b] = []
        if len(b.tail.vertices) == 0: 
            # print("Block ",b," added as trivially sat.")
            self.satisfied_block.add(b)  # check if trivially satisifed
            block_index = b.index()
            if block_index in self.node_weights:
                self.weights[b] = self.node_weights[block_index]
            else:
                # single edge
                self.weights[b] = 1
            self.children[b] = set()
        else:
            self.weights[b] = sys.maxsize
        # else:
        #     self.block_dict[b] = self.hasBasis(b) # basis check

    def minimize_weights(self, topn):
        # new_blocks = blocks that were updated in the last iteration -> continue until there are no more updates
        while self.new_blocks != set():
            new = set() # keep track of newly added blocks to stop when nothing new is added
            for b in self.blocks:
                if len(b.tail.vertices) == 0:
                    # skip trivial blocks
                    continue
                bases = self.determine_bases(b, self.new_blocks)
                #print("bases: " + str(bases))
                all_children = self.top_children[b]
                for basis in bases:
                    #print("basis: " + str(basis))
                    new_weight = self.basis_weight(b, basis)
                    #print("new weight: " + str(new_weight) + ", old weight: " + str(self.weights[b]))
                    #basis_sum = sum(list(map(lambda b: self.weights[b], basis)))
                    weight = self.weights[b]
                    all_children.append(WeightedBasis(new_weight, basis))
                    if new_weight < weight:
                        self.weights[b] = new_weight
                        self.children[b] = basis
                        self.block_to_basis[b] = basis
                        new.add(b)
                #print("all children: ", all_children)
                self.top_children[b] = heapq.nlargest(topn, all_children)
                #print("sorted", self.top_children[b])
            self.new_blocks = new
        if self.weights[self.root_block] == sys.maxsize:
            print("no decomposition found")
            return None
        else:
            decomps = self.construct_tds(topn)
            #decomps = [self.construct_td()]
            print("decompositions found: ")
            for decomp in decomps:
                print(decomp)
                print("weight: ", decomp.weight, "\n")
            #print("root block children", self.children[self.root_block])
            return decomps

    def construct_td(self):
        return self.to_node(self.root_block)
    
    def construct_tds(self, topn):
        return self.to_nodes(self.root_block, topn)

    def add_weights(self, node_costs):
        self.node_weights = node_costs
        
    def add_sj_weights(self, sj_weights):
        self.sj_weights = sj_weights

    def block_weight(self, block):
        cover = list(map(lambda e: e.name, block.cover))
        block_index = ",".join(sorted(cover))
        if block_index in self.node_weights:
            return self.node_weights[block_index]
        else:
            return 1
            
    def sj_weight(self, from_b, to_b):
        cover_from = [e.name for e in from_b.cover]
        idx_from = ",".join(sorted(cover_from))
        cover_to = [e.name for e in to_b.cover]
        idx_to = ",".join(sorted(cover_to))
        idx = idx_from + "-" + idx_to

        if idx in self.sj_weights:
            return self.sj_weights[idx]
        else:
            return 10000000

    def basis_weight(self, block, basis):
        basis_sum = sum(list(map(lambda b: 0 if len(b.tail.vertices) == 0 else self.weights[b], basis)))
        sj_costs = 0
        for b in basis:
            child_basis = self.children[b]
            if len(child_basis) > 0:
                child_block = next(iter(child_basis))
                sj_costs += self.sj_weight(child_block, b)
        return self.block_weight(next(iter(basis))) + sj_costs + basis_sum

    # determine the bases of a block wrt. new blocks (one of the blocks has to be from new_blocks)
    # a basis is a set of blocks
    def determine_bases(self, b, new_blocks):
        bases = []
        #print("block: " + str(b))
        for head in self.head_to_blocks:
            #print("head: " + str(head))
            allBlocks = self.head_to_blocks[head]
            #print("allblocks: " + str(allBlocks))
            #headed_blocks = [x for x in allBlocks if x < b and not (x.head == b.head and x.tail == b.tail)]
            headed_blocks = [x for x in allBlocks if x < b and not (x.head == b.head and x.tail == b.tail)]

            #print("headed blocks: " + str(headed_blocks))

            if set(headed_blocks).intersection(new_blocks) == set():
                continue

            for ob in headed_blocks:
                if self.weights[ob] == sys.maxsize:
                    continue

            # 3. condition (for each component C_i', the block (B', C_i') is satisfied
            cond3 = True
            for ob in headed_blocks:
                if not ob in self.satisfied_block:
                    cond3 = False
            if cond3 == False:
                #print("cond3 broken")
                continue #3nd Condition violated (testing first for efficiency)

            # 1. condition (the tail of the block b is a subset of the union of
            # the tails and the head
            unionTails = set()
            # union of the tails' vertices
            for ob in headed_blocks:
                for v in ob.tail.vertices:
                    unionTails.add(v)
            # add the head's vertices
            for v in head.vertices:
                unionTails.add(v)
            if not b.tail.vertices.issubset(unionTails):
                #print("cond1 broken")
                continue # 1st Condition violated

            # 2. condition (each hyperedge partially contained in the tail of b has to be contained
            # in the union of the tails and the head)
            cond2 = True
            for e in self.H.E:
                if len(e.V.intersection(b.tail.vertices)) == 0:
                    continue # find other edge
                if not e.V.issubset(unionTails):
                    cond2 = False
                    #print("cond2 broken")
                    break
            if cond2 == False:
                continue # 2nd Condition violated

            # basis found!
            basis = set()
            for ob in headed_blocks:
                basis.add(ob)
            bases.append(basis)
            #print("bases: " + str(bases))
        if bases != []:
            self.satisfied_block.add(b)
        return bases

    def hasBasis(self,b):
        basisFound = False
        basisWitness = None
        for B in self.head_to_blocks:
            allBlocks = self.head_to_blocks[B]
            blocks = [x for x in allBlocks if x < b]

            cond3 = True
            for ob in blocks:
                if not ob in self.satisfied_block:
                    cond3 = False
            if cond3 == False:
                continue #3nd Condition violated (testing first for efficiency)

            unionTails = set()
            for ob in blocks:
                for v in ob.tail.vertices:
                    unionTails.add(v)
            for v in B.vertices:
                unionTails.add(v)
            if not  b.tail.vertices.issubset(unionTails):
                continue # 1st Condition violated
            cond2 = True
            for e in self.H.E:
                if len(e.V.intersection(b.tail.vertices)) == 0:
                    continue # find other edge
                if not e.V.issubset(unionTails):
                    cond2 = False
                    break
            if cond2 == False:
                continue # 2nd Condition violated
            basisFound = True
            basisWitness = B
            # print("The basis of ", b , " is ", B)
            # print("The blocks headed by ", B)
            # for BB in blocks:
            #     print(str(BB)+"\n")

            break
        if basisFound == True:
            self.satisfied_block.add(b)
            self.block_to_basis[b] = basisWitness
            return True
        else:
            return False

    def rootHeadFound(self):
        for head in self.head_to_blocks:
            blocks = self.head_to_blocks[head]
            allSatisfied = True
            for b in blocks:
                if not b in self.satisfied_block:
                    allSatisfied = False
            if allSatisfied == True:
                # print("Root Head is ",head)
                self.rootHead = head
                return True
        return False


    def hasDecomp(self):
        while True:            
            changed = False
            for b in self.blocks:
                if b in self.satisfied_block:
                    continue # already marked as satisfied
                res = self.hasBasis(b)
                if res == True:
                    changed = True
                    #print("Found basis for the block ", b)
                if self.rootHeadFound():
                    # print("Found decomp!")
                    return True
            if changed == False:
                # print("Nothing has changed anymore, terminating")
                return False

    def to_node(self,block):
        if not(block in self.satisfied_block):
            # print(block, " is not satisfied")
            return None  # Nothing to return if block not satisfied
        if len(block.tail.vertices) == 0:
            return Node(block.head,self.head_to_cover[block.head],list()) # leaf node
        basis = self.block_to_basis[block]

        node_children = list()
        for block_child in self.children[block]:
            if len(block_child.tail.vertices) != 0:
                node_children.append(self.to_node(block_child))

        basis_head = list(basis)[0].head
        return Node(basis_head,self.head_to_cover[basis_head],node_children)

    def to_nodes(self,block,topn):
        if not(block in self.satisfied_block):
            # print(block, " is not satisfied")
            return None  # Nothing to return if block not satisfied
        if len(block.tail.vertices) == 0:
            # print(block, " is trivial")
            return Node(block.head,self.head_to_cover[block.head],list()) # leaf node

        #print("top basis", self.children[block])
        #print("weight: ", self.weights[block])
        print("top children: ", self.top_children[block])
        nodes = []
        for weighted_basis in self.top_children[block]:
            basis = weighted_basis.basis
            node_children = list()
            for block_child in weighted_basis.basis:
                if len(block_child.tail.vertices) != 0:
                    node_children.append(self.to_node(block_child))

            basis_head = list(basis)[0].head
            nodes.append(Node(basis_head,self.head_to_cover[basis_head],node_children, weighted_basis.weight))
        return nodes

    def getDecomp(self,block):
        if not(block in self.satisfied_block):
            # print(block, " is not satisfied")
            return None  # Nothing to return if block not satisfied
        if len(block.tail.vertices) == 0:
            # print(block, " is trivial")
            return Node(block.head,self.head_to_cover[block.head],list()) # leaf node
        basis = self.block_to_basis[block]
        allBlocks = self.head_to_blocks[basis]
        blocks = [x for x in allBlocks if x < block]

        # print("Child BLocks for block ", block)
        # for bs in allBlocks:
        #     print(bs)

        children = list()
        for bs in blocks: 
            children.append(self.getDecomp(bs))
        
        return Node(basis,self.head_to_cover[basis],children)


    def getDecompRoot(self):
        if self.rootHead == None:
            return None  ## can't find decomp of whole graph if no root head

        allBlocks = self.head_to_blocks[self.rootHead]
        # print("Blocks of RootHead")
        # for bs in allBlocks:
        #     print(bs)


        blocks = [x for x in allBlocks if len(x.tail.vertices) != 0]

        # print("Non-Trivial Blocks of RootHead")
        # for bs in blocks:
        #     print(bs)

        children = list()
        for bs in blocks:
            children.append(self.getDecomp(bs))

        return Node(self.rootHead,self.head_to_cover[self.rootHead],children)