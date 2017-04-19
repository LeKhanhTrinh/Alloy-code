module djisktra
open util/ordering [State] as so
sig Process{}
sig Mutex{}



abstract sig Events{}
one sig Undef, HoldOnMutexE, WaitOnMutexE, ReleaseMutexE extends Events{}

sig HoldsRel{rel : Process -> Mutex}
sig WaitsRel{rel : Process -> Mutex}
sig State{
Holds : HoldsRel,
Waits : WaitsRel,
Ev : Events
}

fact Initial{ 
let s0 = ord/first{ 
s0.Holds.rel = none -> none 
s0.Waits.rel = none -> none 
s0.Ev = Undef 
}
}

fact EventTrigger{
all s : State - ord/last{
let s' = ord/next[s]{
WaitOnMutex[s, s' ] or HoldOnMutex[s, s' ] or ReleaseMutex[s, s' ]
}
}
}

pred WaitOnMutex[s, s' : State]{
some p : Process, m : Mutex{
// Guards
!(p in dom [s.Waits.rel])
m in ran[(dom[s.Holds.rel] - {p}) <: s.Holds.rel]
// Action
s'.Waits.rel = s.Waits.rel + {p -> m}
s'.Holds = s.Holds
s'.Ev = WaitOnMutexE
}
}

run WaitOnMutex
