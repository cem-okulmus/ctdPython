import networkx as nx

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
    def connected(self,H):
        induced = H.vertex_induced_subg(self.head.vertices)
        comps = induced.separate(set())
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