/*
 * Modeling of the relationship between the Kripke model under the LTL
 * semantics of Bounded Model Checking and the domain transition system
 *
 * Author: Daniel Le Berre
 */

-- A state in the domain transition system
sig State {
     successor : set State
}

-- The set of initial states
some sig Initial extends State {
}

-- The set of goal states
some sig Goal extends State {
}

-- The set of reachable states
fun reachable : set State {
   {s: State | some i : Initial | s in i.*successor}
}

-- The set of unreachable states
fun unreachable : set State {
   State - reachable
}

-- A world in a Kripke structure for LTL
sig World {
    wnext : one World,
    states : set State
}

-- The initial world, mapped to the initial states
one sig InitialWorld extends World {
}{states = Initial} 

fact allWorldsAreConnectedToTheInitialWorld {
    all w:World | w in InitialWorld.*wnext	
}

fact linkStateTransitionWithWorldTransition {
    all w: World | w.wnext.states = w.states.successor	
}

fact noDuplicateWorlds {
    no disj w1,w2: World | w1.states= w2.states
}

assert allReachableStatesShouldBeMappedToAWorld {
     reachable in World.states
}

assert noUnreachableStateAreMappedToTheWorlds {
     no World.states & unreachable
}

pred show {
      some State
      #reachable=3
      one Initial
      one Goal
      some Goal & unreachable
}

run show for 4 State, 4 World

check  allReachableStatesShouldBeMappedToAWorld for 5
check noUnreachableStateAreMappedToTheWorlds for 5
