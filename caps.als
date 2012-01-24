open naturals

sig Nonce { }
sig Location { }

// I added this because of an Alloy error that I don't fully
// understand, about being unable to skolemize, if I use "set Nonce"
// in CapServer.implementation below.
sig NonceSet {
  nonces: seq Nonce
}
sig CapServer {
  // Real-world analog:  A domain (www.google.com)
  location: one Location,

  // All the nonces this server knows about---will accumulate as this
  // server sees requests.
  knownCaps: set Nonce,

  // All the nonces created by this server---used to reason about the
  // origin of secrets.
  ownedCaps: set Nonce,

  // Model of arbitrary implementations.  When a request comes in for
  // a given nonce and with a set of nonce arguments, the server
  // responds with 
  implementation: Nonce -> (NonceSet -> NonceSet),

  // A server always exists at some point in time, indicated by a
  // natural
  step: Natural
}

// Two CapServers cannot occupy the same location at the same step.
fact StepsHaveUniqueLocations {
  all disj server, server':CapServer {
    (server.step = server'.step) implies (server.location != server'.location)
  }
}

//A CapServer knows all its owned nonces
fact ServersKnowOwnedCaps {
  all n:Nonce,s:CapServer {
    n in s.ownedCaps implies n in s.knownCaps
  }
}

// OnlyTransitionsChangeStep is an important fact, and should be
// carefully scrutinized.  It is an attempt to ensure that only
// well-defined transitions can change the state of a CapServer.  It
// specifies that for every CapServer, it either:
//   1. Has some previous CapServer that transitioned to it, or
//   2. It was that way at time Zero (initial conditions).
// Note that at the moment a step can be ambiguous, and
// appear to be both an invoke and a grant, for example.  Thus, this
// fact ensures that *at least* one transition applied in the step
// before

fact OnlyTransitionsChangeStep {
  all updated_server:CapServer {
    // The server granted a new capability
    (some server_before_grant:CapServer, granted_nonce:Nonce {
        grant[server_before_grant, updated_server, granted_nonce]
      }) or
    // The server invoked a cap on another server
    (some invoker_before, invokee, invokee':CapServer,
          nonce:Nonce,
          args:NonceSet {
       invoke[invoker_before, updated_server, invokee, invokee', nonce, args]
      }) or
    // The server handled an invocation of one of its caps
    (some invoker, invoker', invokee_before:CapServer,
          nonce:Nonce,
          args:NonceSet {
       invoke[invoker, invoker', invokee_before, updated_server, nonce, args]
      }) or
    // The server decided to change its implementation
    (some server_before: CapServer {
        changeImplementation[server_before, updated_server]
      }) or
    updated_server.step = Zero
  }
}

// Helper
pred sameLocationAndImplementation[server, server':CapServer] {
  server'.location = server.location
  server'.implementation = server.implementation
}

// Helper for indicating a server's state moving forward in time
pred inNextStep[server, server':CapServer] {
  server'.step = server.step.next
}


pred grant[server, server':CapServer, nonce: Nonce] {
  sameLocationAndImplementation[server, server']
  inNextStep[server, server']

  server'.knownCaps = server.knownCaps + nonce
  server'.ownedCaps = server.ownedCaps + nonce
}

pred invoke[invoker, invoker', invokee, invokee': CapServer,
            invokeNonce:Nonce, args: NonceSet] {
	//implementations should be able to change during an invoke
	//a server gets info, so it need to be able to respond to the info
  //sameLocationAndImplementation[invoker, invoker']
	invoker.location = invoker'.location
  inNextStep[invoker, invoker']
  //sameLocationAndImplementation[invokee, invokee']
	invokee.location = invokee'.location
  inNextStep[invokee, invokee']
  //if you are invoking a nonce on yourself, you can only interact with the present you
  invoker.location = invokee.location implies invoker.step = invokee.step

  //neither server can forget nonces during an invoke
  invokee.ownedCaps in invokee'.ownedCaps
  invoker.ownedCaps in invoker'.ownedCaps
  invokee'.knownCaps = invokee.knownCaps + invokeNonce + univ.(args.nonces)
	//use the later invokee's implementation
	//it gives the invokee a chance to react to the invocation
  invoker'.knownCaps = invoker.knownCaps +
    (invokee'.implementation[invokeNonce][args])
  //the invoker should know all the nonces it is passing
  invokeNonce in invoker.knownCaps
  all n:Nonce {
    n in univ.(args.nonces) implies n in invoker.knownCaps
    //the invokee should know all the nonces it is returning
    n in univ.(invokee.implementation[invokeNonce][args].nonces) implies n in invokee.knownCaps
  }
}

pred changeImplementation[server, server':CapServer] {
  server'.location = server.location
  server'.knownCaps = server.knownCaps
  server'.ownedCaps = server.ownedCaps
  inNextStep[server, server']

  server'.implementation != server.implementation
}

