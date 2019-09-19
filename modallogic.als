/*
 * Kripke structure for modal logic
 */

-- A world in a Kripke structure
sig World {
    nextw : set World
}

-- The initial world, mapped to the initial states
one sig InitialWorld extends World {
}

-- Refexivity
pred axiomT {
   all w:World | w in w.nextw
}

-- Symmetry
pred axiomB {
   all w1,w2:World | w2 in w1.nextw implies w1 in w2.nextw
}

-- Seriality
pred axiomD {
   all w: World | some w.nextw
}

-- Transitivity
pred axiom4 {
    all w1,w2,w3:World | w2 in w1.nextw and w3 in w2.nextw implies w3 in w1.nextw
}

-- Euclidean
pred axiom5 {
    all w1,w2,w3:World | w2 in w1.nextw and w3 in w1.nextw implies w3 in w2.nextw
}

assert relationshipAmongAxioms {
    axiom5 and axiomT implies axiomB and axiom4
} 

pred show {
      some World
      axiom5
}

run show for exactly 5 World
check relationshipAmongAxioms for 5 World
