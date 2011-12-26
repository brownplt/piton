open caps

// Sanity.  Ensures that the same CapServer cannot exist in two
// different states at the same timestep
assert SameLocationMeansDifferentStep {
  all disj server, server':CapServer {
    server.location = server'.location implies server.step != server'.step
  }
}
check SameLocationMeansDifferentStep for 5

pred CanGrant[] {
  some s, s':CapServer, n:Nonce | grant[s, s', n]
}

run CanGrantSomething { CanGrant }

pred CanInvoke[] {
  some i, i', e, e':CapServer, n:Nonce, a:NonceSet {
    invoke[i, i', e, e', n, a]
  }
}

run CanInvokeSomething { CanInvoke }

pred CanChange[] {
  some cs, cs':CapServer {
    changeImplementation[cs, cs']
  }
}

run CanChangeSomeImplementation { CanChange }

