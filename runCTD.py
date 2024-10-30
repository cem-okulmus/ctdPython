
from ctdcheck import CTDCheck
from hypergraph import HyperGraph
from functools import partial
from ctdcheck import Block
from ctdcheck import VertSet
import functools
import sys


def all_choose_k(S, k):
    from itertools import chain, combinations
    return chain(*(combinations(S, kp) for kp in range(1,k+1)))
#
def all_lambdas(E, k):
    for es in all_choose_k(E, k):
        # yield set.union(*es)
        yield es

# (over approximates) the bags produced by the LogK algorithm
def computesoftk(h, k):
    softk = list()
    for P in all_lambdas(h.E,k):
        obj1 = set()
        if len(P) == 1:   # this case is just a special case of the general one. Delete?
            obj1 = P[0].V
        elif len(P) > 1:
            obj1 =functools.reduce(lambda a,b: (a).union(b),map(lambda s : s.V,P))
        for C in h.separate(obj1, only_vertices=True):
            for L in all_lambdas(h.E, k):
                obj2 = set()
                if len(L) == 1:
                    obj2 = L[0].V
                elif len(L) > 1:
                    obj2 = functools.reduce(lambda a,b: (a).union(b),map(lambda s : s.V,L))
                B = set.intersection(C, obj2)
                if len(B) > 1 and B not in softk:
                    softk.append((B,L))
    return softk
    
# computes the blocks of a bag by computing its components w.r.t. h
def bag_to_blocks(h,pair):
    B = pair[0]
    L = pair[1]  
    blocks = list()
    for C in h.separate(B, only_vertices=True):
        blocks.append(Block(VertSet(B),L,VertSet(C)))
    blocks.append(Block(VertSet(B),L,VertSet(set())))  # adding trivial block too
    return blocks



# connected lambda a,h : a.connected(h)
def bag_to_blocks_constraint(h,constraint, pair): 
    # print("pair: ", pair)
    blocksPrefilter = bag_to_blocks(h,pair)
    return filter(constraint,blocksPrefilter)
    # return blocksPrefilter


# # computes the blocks of a bag by computing its components w.r.t. h
# def bag_to_blocksConnected(h,pair):
#     B = pair[0]
#     L = pair[1]  
#     blocks = list()
#     for C in h.separate(B, only_vertices=True):
#         tempBlock = Block(VertSet(B),L,VertSet(C))
#         if tempBlock.connected(h):
#             blocks.append(tempBlock)
#     tmp = Block(VertSet(B),L,VertSet(set()))
#     if tmp.connected(h):
#         blocks.append(tmp)  # adding trivial block too
#     return blocks


# Same as  computeosftK, but returns directly the blocks
def computesoftkBlocks(h, k):
    out = list()
    listOfLists = map(partial(bag_to_blocks,h),computesoftk(h,k))
    for ll in listOfLists:
        for l in ll:
            out.append(l)
    return out



# Same as  computeosftK, but returns directly the blocks
def computesoftkBlocksConstraint(h, k,constraint):
    out = list()
    listOfLists = map(partial(bag_to_blocks_constraint,h,constraint),computesoftk(h,k))
    for ll in listOfLists:
        for l in ll:
            out.append(l)
    return out


# # Same as  computeosftK, but returns directly the blocks
# def computesoftkBlocksConnected(h, k):
#     out = list()
#     listOfLists = map(partial(bag_to_blocksConnected,h),computesoftk(h,k))
#     for ll in listOfLists:
#         for l in ll:
#             out.append(l)
#     return out



# h = HyperGraph.fromHyperbench("/home/okulmus/Documents/OldBenchmarks/benchmark/hyperbench/1.dtl")
h = HyperGraph.fromHyperbench(sys.argv[1])


# print("all Lambdas for k 2 ")
# for sep in all_lambdas(h.E,3):
#     print(sep)
#     obj1 = set()
#     if len(sep) == 1:
#         obj1 = sep[0].V
#     elif len(sep) > 1:
#         print("Type sep ", type(sep), sep )
#         obj1 = functools.reduce(lambda a,b: (a).union(b),map(lambda s : s.V,sep))
#     print("sep ", sep, " of type ", type(sep) ," has vertex set ", obj1, " type ", type(obj1))

ctd = CTDCheck(h)

# blocks = computesoftkBlocksConnected(h,2)
# blocks = computesoftkBlocksConnected(h,int(sys.argv[2]))
blocks = computesoftkBlocksConstraint(h,int(sys.argv[2]), lambda b: b.connected())

for b in blocks:
    # print("Adding blocks ", b)
    ctd.addBlock(b)
    # headedBy = ctd.head_to_blocks[repr(b.head)]
    # print("All blocks headed by ",b.head )
    # for h in headedBy:
        # print(h)


print("Done adding blocks")

print("Running hasDecomp")

res = ctd.hasDecomp()

print("hasDecomp done. Result: ",res)

decomp = ctd.getDecompRoot()

if decomp is not None:
    print("Found decomposition \n", decomp)
    print("Decomp correct: "  + str(decomp.isCorrect(h)) )