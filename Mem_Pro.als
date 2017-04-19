module MemoryProtection

//Memory
sig Memory{
	belong: lone OS_Obj,
	belongs: lone OS_App
}

sig  DataSections, Stacks extends Memory{}

//OS Object
sig OS_Obj{
	datasec: some DataSections,
	stack: some Stacks
//	access: OS_Obj -> some OS_Obj
}

sig Tasks, ISRs extends OS_Obj{}
sig Cate_1, Cate_2 extends ISRs{}

//OS App
sig OS_App{
	private_data: some DataSections,
	elements: some Tasks,
	map: OS_App -> elements.datasec
}

sig Trusted_OS, NonTrusted_OS extends OS_App{}

// Accesses


sig OSObj_Access{
	map: OS_Obj -> OS_Obj.datasec
}

sig Stack_Access{
	map: OS_Obj -> OS_Obj.stack
}
// constraints
fact{
	Cate_1 + Cate_2 = ISRs
	Trusted_OS + NonTrusted_OS = OS_App
	DataSections + Stacks = Memory
	Tasks + ISRs = OS_Obj
	OS_App in P(OS_Obj)
}

pred show[m: OSApp_Access]{
	#m.map > 1
}

run show for 2 but 1 OSApp_Access
// 
