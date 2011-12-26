// Did my own numbers because I was learning, they seem to work fine.
// They are used to represent time steps for servers updating state.

// There might not be a next natural, because there is a max number we can
// represent
sig Natural {next:lone Natural}
fact {
  // Naturals don't appear ahead of themselves
  all n:Natural | not (n in n.^next)
  // If it has a next, it has a predecessor, unless its Zero
  all n:Natural {
    (some n':Natural | n' in n.next) implies
     ((some n'':Natural | n in n''.next) or n = Zero)
  }
}
one sig Zero in Natural {}
lone sig One, Two, Three, Four, Five in Natural {}
fact {
  One in Zero.next
  Two in One.next
  Three in Two.next
  Four in Three.next
  Five in Four.next
}
