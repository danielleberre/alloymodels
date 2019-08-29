/*
 * Modeling of the relationship between the Kripke model under the LTL
 * semantics of Bounded Model Checking and the domain transition system
 *
 * Author: Daniel Le Berre
 */

-- A state in the domain transition system
sig State {
     nexts : set State
}

-- The set of initial states
some sig Initial extends State {
}

-- The set of goal states
some sig Goal extends State {
}

-- The set of reachable states
fun reachable : set State {
   {s: State | some i : Initial | s in i.*nexts}
}

-- The set of unreachable states
fun unreachable : set State {
   State - reachable
}

-- A world in a Kripke structure for LTL
sig World {
    nextw : one World,
    states : set State
}

-- The initial world, mapped to the initial states
one sig InitialWorld extends World {
}{states = Initial} 

fact allWorldsAreConnectedToTheInitialWorld {
    all w:World | w in InitialWorld.*nextw	
}

fact linkStateTransitionWithWorldTransition {
    all w: World | w.nextw.states = w.states.nexts	
}

fact noDuplicateWorlds {
    no disj w1,w2: World | w1.states= w2.states
}

-- simple case with 4 states, one initial state and one goal state,
-- goal state not reachable
pred show {
      #reachable=3
      one Initial
      one Goal
      some Goal & unreachable
}

run show for 4 State, 4 World

-- properties that can be checked on that specification

assert allReachableStatesShouldBeMappedToAWorld {
     reachable in World.states
}

assert noUnreachableStateAreMappedToTheWorlds {
     no World.states & unreachable
}

check allReachableStatesShouldBeMappedToAWorld for 5
check noUnreachableStateAreMappedToTheWorlds for 5
