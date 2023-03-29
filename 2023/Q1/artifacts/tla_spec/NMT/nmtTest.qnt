// -*- mode: Bluespec; -*-

module basics{

    type BINARY = List[int]

    def binary(n: int) : BINARY =
        if (n == 0)
            [0]
        else
            range(0,n).foldl(
                [],
                (acc, i) => {
                    val c = n / 2^i
                    if (c > 0)
                        [c % 2].concat(acc)
                    else
                        acc
                }
            )
    
    // this function gets the first power of 
    // 2 which is greater than `lastNode`
    def getFullTreeSize(lastNode : int) : int =
       if (lastNode == 0)
            1
        else
            2^length(binary(lastNode))
    
    def sum(list: List[int]) : int =
        list.foldl(0, (acc, i) => acc + i)
    
    def min(S: Set[int]) : int = 
        // val tentativeMin = chooseSome(S) ---> chooseSome is not supported yet
        val tentativeMin = -1
        S.fold(
            tentativeMin, 
            (acc, i) => if ((acc == tentativeMin) or (i < acc)) i else acc
            )

    def listToSet(S: List[int]) : Set[int] = 
        S.foldl(Set(), (acc, i) => acc.union(Set(i)))


    def setToSortedList(S: Set[int]) : List[int] = 
        S.fold(
            [], 
            (acc, i) => acc.concat(
                [min(S.exclude(listToSet(acc)))]
                )
            )

    def max(S: Set[int]) : int = 
        // val tentativeMax = chooseSome(S) --> chooseSome not supported yet
        val tentativeMax = -1
        S.fold(
            tentativeMax, 
            (acc, i) => if ((acc == -1) or (i > acc)) i else acc
            )
    
        
    

    def reverse(L: List[x]) : List[x] =
        L.foldl([], (acc, i) => [i].concat(acc))

    def getWithDefault(mapX: int -> a, key: int, default: a) : a =
        if (mapX.keys().contains(key))
            mapX.get(key)
        else
            default        


}

module nmt_helpers{

    type NODE_IDX = int

    // hashes will be of type WORD
    type WORD = List[(str, int)]


    def getParentIdx(idx : NODE_IDX) : NODE_IDX =
        idx / 2

    def getLeftChildIdx(idx : NODE_IDX) : NODE_IDX =
        2 * idx

    def getLeftUncleIdx(idx : NODE_IDX, uncle_level : int) : NODE_IDX =
        idx/2^uncle_level - 1

    def getRightUncleIdx(idx : NODE_IDX, uncle_level : int) : NODE_IDX =
        idx/2^uncle_level + 1


    def getRightChildIdx(idx : NODE_IDX) : NODE_IDX =
        2 * idx + 1

    def Hash(data: WORD) : WORD =
        data

    def mergeWithLeftAndRight(left: WORD, middle: WORD, right: WORD) : WORD =
        concat(concat(left, middle), right)


    // takes a list and maps it to a new list which contains hashes 
    // of consecutive pairs of elements from the original list
    def pairwiseHash(dataList: WORD) : WORD =
        
        if (length(dataList) == 1)
            dataList
        else
            range(0, length(dataList)).foldl(
                [],
                (acc, i) => {
                    if (i % 2 == 0)
                        acc
                    else
                        acc.concat(Hash(concat([dataList[i-1]],[dataList[i]])))
                }
            )      
    }

module nmtTest {    
    import basics.*
    import nmt_helpers.*
    

    // ASSUMPTION: each tree is full and complete (2^n leaves at the bottom level)
    

    
    pure val MAX_POWER = 5
    pure val MAX_NAMESPACE_ID = 100
    pure val EMPTY_PROOF = {start: -1, end: -1, supporting_hashes: []}
    pure val EMPTY_TREE = {leaves: Map(), hashes: Map()}
    pure val EMPTY_LEAVES = []

    
    var proof_v : PROOF
    var tree_v : TREE    
    var namespace_v : int    
    var next_state_v : string
    var leaves_v : List[DATA_ITEM]
    var corrupted : bool
    var corruption_type : string
    var corruption_diff : {changed_start: int, changed_end: int, changed_namespace: int, changed_indices: List[int]}

    

    // each tree is a mapping from node indices (=integers) to the
    // corresponding data at leaf nodes and hashes of all nodes.
    // the root of the tree has index 1, its child 2 and 3 etc. (as captured in functions
    // `getParentIdx`, `getLeftChildidx` and `getRightChildIdx`)
    // 
    type TREE = {
        leaves: NODE_IDX -> DATA_ITEM,        
        hashes: NODE_IDX -> NAMESPACE_HASH      
    }

    type NAMESPACE_HASH = {minNS: int, maxNS: int, hash: WORD}
    
    type PROOF = {start: int, end: int, supporting_hashes: List[NAMESPACE_HASH]}

    type DATA = (str, int)

    type DATA_ITEM  = {value: DATA, namespaceId: int}



    def GenerateLeavesCorrectly(power: int, namespaceBordersSet : Set[int]) : List[DATA_ITEM] =
        
        // add left-most and right-most borders to namespaces
        val namespaceBorders = concat(
            concat([0], setToSortedList(namespaceBordersSet)),
            [2^(power-1)]
        )        
        
        val generated_leaves_dummy_hash : List[DATA_ITEM] = 
            // for each namespace
            range(0, length(namespaceBorders)-1).foldl(
                [],
                (acc, i) => 
                    acc.concat(
                        // and for each leaf between two namespaces
                        range(namespaceBorders[i], namespaceBorders[i+1]).foldl(
                            [],
                            // create a data point
                            (acc2, j) => acc2.concat([{value: ("data", 0), namespaceId: i*2}])
                            )
                        )
            )

        // this is mostly for debugging purposes: have data value correspond exactly to the index
        // of the leaf. (This enables easier reasoning about the generated proofs later)
        val generated_leaves : List[DATA_ITEM] = 
            range(0, length(generated_leaves_dummy_hash)).foldl(
                [],
                (acc, i) => acc.concat(                    
                    [{value: ("data", i), namespaceId: generated_leaves_dummy_hash[i].namespaceId}]
                )
        )

        generated_leaves




    def BuildTree(leaves: List[DATA_ITEM]) : TREE = 
        // because of the way trees are represented (nodes enumerated from 1 to 2^n - 1),
        // and the assumption of full and complete trees, we know that leaves
        // are occupying the half of the tree. Thus, their starting index equals their length
        val leaf_idx_start = length(leaves)

        val tree_leaves : NODE_IDX -> DATA_ITEM = 
            range(0, length(leaves)).foldl(
                Map(),
                (acc, i) => acc.put(leaf_idx_start + i, leaves[i])
            )

        val tree_leaves_hashes : NODE_IDX -> NAMESPACE_HASH = 
            range(0, length(leaves)).foldl(
                Map(),
                (acc, i) => 
                acc.put(
                    leaf_idx_start + i, 
                    {minNS: leaves[i].namespaceId, maxNS: leaves[i].namespaceId, hash: Hash([leaves[i].value])})
            )

        // starting from leaves, calculating the hashes for all other nodes 
        // of the tree
        val tree_hashes : NODE_IDX -> NAMESPACE_HASH = 
            reverse(range(1, leaf_idx_start)).foldl(
                tree_leaves_hashes,
                (acc, i) =>
                acc.put(
                    i,
                    {
                        // minimum is the minimum of the left child because of the ordering assumption
                        minNS: acc.get(getLeftChildIdx(i)).minNS,
                        // max is the max of the right child because of the ordering assumption
                        maxNS: acc.get(getRightChildIdx(i)).maxNS,
                        hash: Hash(
                            concat(
                                acc.get(getLeftChildIdx(i)).hash,
                                acc.get(getRightChildIdx(i)).hash
                            )
                        )
                    }
                )  
        )

        {leaves: tree_leaves, hashes: tree_hashes}
    

    def CreateProofNamespace(namespaceId: int, tree: TREE): PROOF =
        val leavesStart = min(tree.leaves.keys())                
        // take only those keys that are of the desired namespace
        val relevantLeavesKeys = tree.leaves.keys().fold(
            Set(),
            (acc, i) => 
                if (tree.leaves.get(i).namespaceId == namespaceId)
                    union(acc, Set(i))
                else
                    acc            
        )
        val start = min(relevantLeavesKeys)        

        // we want to get the binary representation of the number leaves from the `start` (first node of the 
        // leaves that go to the proof) and the very beginning of leaves because this encodes left siblings, 
        // uncles, etc., which are needed for the merkle proof. The fact that we use it reversed is because the 
        // proof defines the nodes to be in-order, thus, older ancestors come first (bcs they are more left)
        val binaryLeftLimitDistanceReversed = reverse(binary(start - leavesStart))
        
        val left_hashes : List[NAMESPACE_HASH] = 
            range(0, length(binaryLeftLimitDistanceReversed)).foldl(
                [],
                (acc, i) =>
                    if (binaryLeftLimitDistanceReversed[i] == 1)                    
                        concat([tree.hashes.get(getLeftUncleIdx(start, i))], acc)
                    else
                        acc
                )

        val end = max(relevantLeavesKeys)
        val binaryRightLimitDistanceReversed = reverse(binary(2*leavesStart-1 - end))

        val right_hashes : List[NAMESPACE_HASH] = 
            range(0, length(binaryRightLimitDistanceReversed)).foldl(
                [],
                (acc, i) =>
                    if (binaryRightLimitDistanceReversed[i] == 1)                    
                        acc.concat([tree.hashes.get(getRightUncleIdx(end, i))])
                    else
                        acc
                )            

        // start needs to be expressed relative to leaves start and so does end. 
        {
            start: start - leavesStart, 
            // the +1 is because the range has to be non-inclusive at the right side
            end: end - leavesStart +1, 
            supporting_hashes: concat(left_hashes, right_hashes)
        }

    

    



    
    action init = {              
        all{            
            tree_v' = EMPTY_TREE,
            proof_v' = EMPTY_PROOF,
            corrupted' = false,
            next_state_v' = "init",
            namespace_v' = -1,
            leaves_v' = EMPTY_LEAVES,
            corruption_type' = "",
            corruption_diff' = 
            {
                changed_start: -1,
                changed_end: -1,
                changed_namespace: -1,
                changed_indices: []
            }

        }        
    }

    action requirements = {
        all{
            // state precondition
            ((next_state_v == "requirements") or (next_state_v == "init")),
            // update state for the next step
            next_state_v' = "generation",

            nondet power = oneOf(3.to(MAX_POWER))  
            //TODO: there must be a better way to generate this set
            nondet namespaceBordersSet = 1.to(2^(power-1) - 2).powerset().filter(x => size(x) > 1).oneOf()
            val leaves = GenerateLeavesCorrectly(power, namespaceBordersSet)
            all{                    
                val tree = BuildTree(leaves)
                all{
                    leaves_v' = leaves,
                    tree_v' = tree,
                    nondet namespaceId = tree.leaves.keys().fold(
                        Set(),
                        (acc, leaf_key) => 
                        union(acc, Set(tree.leaves.get(leaf_key).namespaceId))                    
                    ).oneOf()                 
                    namespace_v' = namespaceId,
                }
            },
            // unchanged variables
            proof_v' = proof_v,                
            corrupted' = corrupted,
            corruption_type' = corruption_type,
            corruption_diff' = corruption_diff
            }
    }

    action generation = {
        all{
            // state preconditions
            next_state_v == "generation",
            // update state for the next step
            next_state_v' = "final",
            proof_v' = CreateProofNamespace(namespace_v, tree_v),
            // unchanged variables
            namespace_v' = namespace_v,
            corrupted' = false,
            tree_v' = tree_v,
            leaves_v' = leaves_v,
            corruption_type' = corruption_type,
            corruption_diff' = corruption_diff            
        }
    }


   



    action final = {
        all {
            // state preconditions
            next_state_v == "final",
            //update state for the next step
            next_state_v' = "requirements",
            // resetting the state to initial values
            namespace_v' = -1,
            tree_v' = EMPTY_TREE,
            proof_v' = EMPTY_PROOF,
            corrupted' = false,
            leaves_v' = EMPTY_LEAVES,
            corruption_type' = "",
            corruption_diff' = 
            {
                changed_start: -1,
                changed_end: -1,
                changed_namespace: -1,
                changed_indices: []
            }
            }
    }

    action corruptProof = {
        all{
            // state preconditions
            next_state_v == "final",
            corrupted == false,

            // corrupting the proof
            any{
                // corrupting the start value
                all{
                    proof_v.end != 1,
                    namespace_v' = namespace_v,
                    nondet new_start = oneOf(
                        0.to(proof_v.end - 1).exclude(Set(proof_v.start))
                        )
                    all{
                                        
                        proof_v' = {start: new_start, end: proof_v.end, supporting_hashes: proof_v.supporting_hashes},                        
                        corruption_type' = "start",                        
                        corruption_diff' = corruption_diff.with("changed_start", new_start),
                    }
                },

                // corrupting the end value
                all{
                    proof_v.start < proof_v.end - 1,
                    namespace_v' = namespace_v,
                    nondet new_end = oneOf(proof_v.start.to(proof_v.end - 1))
                    all{
                        proof_v' = {start: proof_v.start, end: new_end, supporting_hashes: proof_v.supporting_hashes},
                        corruption_type' = "end",
                        corruption_diff' = corruption_diff.with("changed_end", new_end),
                    }
                    
                },
                
                // corrupting the supporting hashes in a controlled way
                all{
                    proof_v.supporting_hashes.length() > 1,
                    namespace_v' = namespace_v,
                    nondet new_supporting_hashes_indices = oneOf(
                        0.to(proof_v.supporting_hashes.length()-1)
                            .powerset()
                            .filter(
                                x => 
                                and{
                                    size(x) < proof_v.supporting_hashes.length(),
                                    size(x) > 0
                                }
                        )
                    )
                    val new_supporting_hashes = range(0, proof_v.supporting_hashes.length())
                        .foldl(
                            [],
                            (acc, i) => 
                            if (new_supporting_hashes_indices.contains(i))
                                acc.append(proof_v.supporting_hashes[i])
                            else
                                acc
                        )          
                    all{          
                        proof_v' = {start: proof_v.start, end: proof_v.end, supporting_hashes: new_supporting_hashes},
                        corruption_type' = "supporting_hashes",
                        val new_indices = range(0, proof_v.supporting_hashes.length())
                            .foldl(
                                [],
                                (acc, i) => 
                                if (new_supporting_hashes_indices.contains(i))
                                    acc.append(i)
                                else
                                    acc
                            )
                        corruption_diff' = corruption_diff.with("changed_indices", new_indices),
                    }
                    
                },
                
                // corrupting the namespace value
                all{                 
                    proof_v' = proof_v,
                    nondet newNamespace = 1.to(MAX_NAMESPACE_ID).exclude(Set(namespace_v)).oneOf()
                    all{
                        namespace_v' = newNamespace,
                        corruption_type' = "namespace",
                        corruption_diff' = corruption_diff.with("changed_namespace", newNamespace),
                    }
                }
            },            
            corrupted' = true,

            // unchanged variables
            next_state_v' = next_state_v,
            tree_v' = tree_v,            
            leaves_v' = leaves_v
        }
        

    }

    // step is modelled as a loop of four always repeating states: 
    // 1) requirements, 2) generation,  3) verification, and 4) final state.
    // 
    // 1) when in the "requirements" or "init" state, a random size of the tree and the namespaces 
    // corresponding to leaves,
    // are generated and one of the namespaces is chosen to generate a proof for
    // 2) when in the "generation" state, a proof is generated for the generated tree and the chosen namespace
    // 3) when in the "verification" state, that proof is verified
    // 
    // The three steps happen one after another (no non-determinism involved)
    action step = {
        any{

            // 1): requirements: defining the tree and the namespace to generate a proof for
            requirements,

            // 2): generation of the proof 
            generation,
            
            // 2b): corrupting the proof
            corruptProof,            

            // 3): collecting all results
            final
            
        }

    }
    

}