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
    -- Since we are in BMC, we may have a world without successor
    nextw : lone World,
    states : set State
}

-- The initial world, mapped to the initial states
one sig InitialWorld extends World {
}{states = Initial} 

fun lastworld : set World {
    { w : World | no w.nextw }
}

-- does the Kripke structure contains a lasso, a loop?
pred hasLasso {
    some w:World | w in w.^nextw
}

fact allWorldsAreConnectedToTheInitialWorld {
    all w:World | w in InitialWorld.*nextw	
}

fact linkStateTransitionWithWorldTransition {
    all w: World | w.nextw.states = w.states.nexts	
}

fact noDuplicateWorlds {
    no disj w1,w2: World | w1.states= w2.states
}

fact lastWorldContainsGoalIfReachable {
    some (Goal & lastworld.states) || Goal in unreachable 
}
-- simple case with 4 states, one initial state and one goal state,
-- goal state not reachable
pred show {
      #reachable>=3
      one Initial
      one Goal
      hasLasso
}

run show for 4 State, 4 World

-- properties that can be checked on that specification

assert ifGoalNotReachableAllReachableStatesShouldBeMappedToAWorld {
     some (Goal & lastworld.states) || reachable in World.states
}

assert noUnreachableStateAreMappedToTheWorlds {
     no World.states & unreachable
}

assert ifTheStructureHasALassoThenGoalIsNotReachable {
     hasLasso implies Goal in unreachable
}

assert thereIsAtMostOneLastWorld {
     #lastworld <= 1
}

check ifGoalNotReachableAllReachableStatesShouldBeMappedToAWorld for 6
check noUnreachableStateAreMappedToTheWorlds for 6
check ifTheStructureHasALassoThenGoalIsNotReachable for 6
check thereIsAtMostOneLastWorld for 6
