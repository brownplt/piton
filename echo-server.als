open caps

// echoServers always return the caps they were invoked with
pred echoServer(l:Location) {
  all server:CapServer {
    server.location = l implies
      {
        all n:Nonce, ns:NonceSet {
          server.implementation[n][ns] = ns
        }
      }
  }
}

pred SomeEchoServer {
  some s:CapServer {
    echoServer[s.location] and
    some n':Nonce, ns:NonceSet {
      not (ns = none) and
      not (s.implementation[n'][ns] = none)
    }
  }
}

//run SomeEchoServer

// Asserts that the invoker's knownCaps don't change by more than the
// nonces in the arguments
assert EchoServersDontLeak {
  all l:Location {
    echoServer[l] implies
      {
        all s,s',i,i':CapServer, n:Nonce, ns:NonceSet {
          (invoke[i,i',s,s',n,ns] and s.location = l) implies
            {
              (i'.knownCaps - i.knownCaps) in ns.nonces
            }
        }
      }
  }
}
check EchoServersDontLeak for 5
