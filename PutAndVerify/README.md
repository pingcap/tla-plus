# Put and Verify Committing

This algorithm allows you write to a file exactly-once in a object storage 
supports `PUT` and `LIST` and the two operations have strong consistency.

The model constants:

- `CLIENTS`: The participants of the algorithm.
- `WITH_CRASHING`: Allow any of participants crash after sending a write message before receiving a response.
- `WITH_RO`: Allow "read-only" clients to participate. The algorithm then becomes a `RWLock` implementation: *many of "read-only" clients commit* or *exactly one of "read-write" client commits*.