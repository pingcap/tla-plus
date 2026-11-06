module memdb {
    import basicSpells.* from "./basicspells"
    type Key = int
    type Value = int
    type Request = {id: int, generation: int, kvs: Set[(Key, Value)]}
    type Response = {id: int}

    pure def minKey = 1
    pure def maxKey = 10
    pure def minValue = 0
    pure val maxValue = 10

    // state ========================================

    // a simple map that is used to check against
    var correctDB: Key -> Value

    var mutableDB: Key -> Value
    // the one that is in flush
    var immutableDB: Key -> Value
    // the ids of requests that the client is waiting for. 
    // It means client will handle a response only once (no matter how many times it retried).
    // Note the response may not be from the first request, it can come from a retry request, and the resp of the first req is lost.
    // Client only handles responses whose id is in the tracker
    // When client receieves a response, or when client retries a request, it drops the id of the request.
    var clientWaitingReqIds: Set[int]

    // mock TiKV
    var tikvDB: Key -> {generation: int, value: Value}
    
    var writtenKeys: Set[Key]
    // requests are always in flight, so it naturally imitates network retries.
    // If we wanna make differences when retrying, e.g. attach a retry flag. Modify this.
    var inflightRequests: Set[Request]
    var inflightResponses: Set[Response]
    var nextID: int
    var nextGeneration: int

    // functions ====================================

    val state = {
        correctDB: correctDB,
        writtenKeys: writtenKeys,
        mutableDB: mutableDB,
        immutableDB: immutableDB,
        tikvDB: tikvDB,
        inflightRequests: inflightRequests,
        inflightResponses: inflightResponses,
        nextID: nextID,
    }

    def readFromcorrectDB(k: Key):Value = {
        correctDB.get(k)
    }

    def read(k: Key): Value = {
        if (mutableDB.has(k)) {
            mutableDB.get(k)            
        } else if (immutableDB.has(k)) {
            immutableDB.get(k)
        } else if (tikvDB.has(k)) {
            tikvDB.get(k).value
        } else {
            -1
        }
    }


    // actions ======================================

    action unchanged = all {
        correctDB' = correctDB,
        writtenKeys' = writtenKeys,
        mutableDB' = mutableDB,
        tikvDB' = tikvDB,
        immutableDB' = immutableDB,
        inflightRequests' = inflightRequests,
        inflightResponses' = inflightResponses,
        nextID' = nextID,
        nextGeneration' = nextGeneration,
        clientWaitingReqIds' = clientWaitingReqIds,
    }

    action write(k: Key, v: Value): bool = all {
        size(writtenKeys) <= 5,
        correctDB' = correctDB.put(k,v),
        writtenKeys' = writtenKeys.union(Set(k)),
        mutableDB' = mutableDB.put(k,v),
        tikvDB' = tikvDB,
        immutableDB' = immutableDB,
        inflightRequests' = inflightRequests,
        nextID' = nextID,
        nextGeneration' = nextGeneration,
        inflightResponses' = inflightResponses,
        clientWaitingReqIds' = clientWaitingReqIds,
    }

    action send(req: Request): bool = all {
        inflightRequests' = inflightRequests.union(Set(req)),
        clientWaitingReqIds' = clientWaitingReqIds.union(Set(req.id)),
    }

    action flush = all {
        size(immutableDB.keys()) == 0,
        immutableDB' = mutableDB,
        mutableDB' = Map(),

        // Assumption: there is only one batch that contains all keys. In this spec we don't care about batches
        send(
                {
                    id: nextID,
                    kvs: mutableDB.keys().map(k => (k, mutableDB.get(k))),
                    generation: nextGeneration,
                }
            ),
        nextID' = nextID + 1,
        nextGeneration' = nextGeneration + 1,
        writtenKeys' = writtenKeys,
        tikvDB' = tikvDB,
        correctDB' = correctDB,
        inflightResponses' = inflightResponses,
    }

    action doTikvWrite(req: Request): bool = all {
        req.kvs.forall(kv => tikvDB.getOrElse(kv._1, {generation: -1, value: -1}).generation < req.generation),
        tikvDB' = req.kvs.fold(tikvDB, (db, kv) => db.put(kv._1, {generation: req.generation, value: kv._2})),
        inflightResponses' = inflightResponses.union(Set({id: req.id})),
        inflightRequests' = inflightRequests,
        mutableDB' = mutableDB,
        immutableDB' = immutableDB,
        writtenKeys' = writtenKeys,
        correctDB' = correctDB,
        nextID' = nextID,
        nextGeneration' = nextGeneration,
        clientWaitingReqIds' = clientWaitingReqIds,
    }

    // This is for test only, specify the request to process in TiKV
    action doTikvWriteWithId(id: int): bool = {
        nondet req = oneOf(inflightRequests.filter(r => r.id == id))
        doTikvWrite(req)
    }

    action tikvWrite: bool = all {
        size(inflightRequests) > 0,
        {
            nondet req = oneOf(inflightRequests)
            doTikvWrite(req)    
        }
    }

    action clientReceiveResponse = {
        val validRespSet = inflightResponses.filter(resp => clientWaitingReqIds.contains(resp.id))
        all {
            size(validRespSet) > 0,   
            nondet resp = oneOf(validRespSet)
            nondet req = oneOf(inflightRequests.filter(r => r.id == resp.id))
            doClientReceiveResponse(resp, req)
        }
    }
    

    action doClientReceiveResponse(resp: Response, req: Request): bool = all {
        inflightResponses' = inflightResponses.setRemove(resp),
        immutableDB' = immutableDB.mapRemoveAll(req.kvs.map(kv => kv._1)),
        inflightRequests' = inflightRequests,
        mutableDB' = mutableDB,
        writtenKeys' = writtenKeys,
        tikvDB' = tikvDB,
        correctDB' = correctDB,
        nextID' = nextID,
        nextGeneration' = nextGeneration,
        clientWaitingReqIds' = clientWaitingReqIds.setRemove(req.id),
    }

    action init() = all {
        correctDB' = Map(),
        writtenKeys' = Set(),
        mutableDB' = Map(),
        immutableDB' = Map(),
        tikvDB' = Map(),
        inflightRequests' = Set(),
        inflightResponses' = Set(),
        nextID' = 1,    
        clientWaitingReqIds' = Set(),
        nextGeneration' = 1,
    }

    action step() = {
        nondet k = oneOf(minKey.to(maxKey))
        nondet v = oneOf(minValue.to(maxValue))
        any {
            // user action
            write(k,v),
            // client action
            flush,
            clientReceiveResponse,
            // server action
            tikvWrite,
        }
    }

    // Tests ========================================

    run retryRequestOverWrite = init
                                .then(write(1,1))
                                .then(flush)
                                .then(doTikvWriteWithId(1))
                                .then(clientReceiveResponse)
                                .then(write(1,2))
                                .then(flush)
                                .then(doTikvWriteWithId(2))
                                .then(clientReceiveResponse)
                                .then(doTikvWriteWithId(1))
                                .fail() // stale req cannot succeed

    // Invariants and properties ====================
    
    val typeOK = all {
        forall(correctDB.keys(), k => {
            correctDB.get(k) >= minValue and correctDB.get(k) <= maxValue
        })
    }

    val equivalence = {
        forall(writtenKeys, k => {
            readFromcorrectDB(k) == read(k)
        })
    }
}