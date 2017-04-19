module Context

sig OS_App{obj: OS_Object}
sig Trusted_OS, NonTrusted_OS extends OS_App{}
sig OS_Object{element: Memory}
sig Tasks, ISRs extends OS_Object{}
sig Memory{}
sig Stacks, Datasections extends Memory{}
sig ISR1, ISR2 extends ISRs{}

sig ObjData{
	objdata: OS_Object -> lone Datasections
}

sig ObjStack{
	objstk: OS_Object -> lone Stacks
}

sig AppData{
	appdata: OS_App -> lone Memory
}

fact eachObjectBelongToOneOS{
	all obj:OS_Object | some os:OS_App | obj in os
}

pred show{
	
}

run show for 2
