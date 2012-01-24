open caps

pred CryptographicGrants(l:Location) {
  all server,server':CapServer, n:Nonce {
    //if a nonce is owned by two servers and one of them is at location l, the other must be at location l
    (n in server.ownedCaps and n in server'.ownedCaps and l = server.location) implies (l = server'.location)
    //if a nonce is owned by a server at location l, it cannot be known by any other server at step zero
    (n in server.ownedCaps and l = server.location and
      n in server'.knownCaps and Zero = server'.step) implies (l = server'.location)
    //if a server at location l ever owns a nonce, it created the nonce, so every server at location
    //l should own the nonce if it owns the nonce (the nonce didn't exist before some server at location
    //l created it, and once it was created, every server at l both knows and owns it)
    (l = server.location and l = server'.location and
     n in server.ownedCaps and n in server'.knownCaps) implies n in server'.ownedCaps
  }
}

pred NoGrantedAccess(l:Location) {
  //all servers at l don't return an owned nonce
  all server:CapServer {
    (server.location = l) implies
    all n,n':Nonce, ns:NonceSet, i:Int {
      (i->n' in server.implementation[n][ns].nonces) implies (n' not in server.ownedCaps)
    }
  }
  //all servers at l don't use an owned nonce in an invocation
  all n,n':Nonce, ns:NonceSet, invoker,invoker',invokee,invokee':CapServer {
    (invoker.location = l and n in invoker.ownedCaps and
    invoke[invoker,invoker',invokee,invokee',n',ns]) implies (not (n = n' or n in univ.(ns.nonces)))
  }
}

assert SufficientParanoidServer {
  all l:Location {
    (CryptographicGrants[l] and NoGrantedAccess[l]) implies
    all n:Nonce, s,s':CapServer {
      (n in s.ownedCaps and s.location = l and n in s'.knownCaps) implies (s'.location = l)
    }
  }
}

check SufficientParanoidServer for 5
