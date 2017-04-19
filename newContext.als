module theContext

sig Status{}
// Memory contains DataSections and Stacks
sig Memory {
	parent : lone OS_Object, 
	data: some DataSections,
	stack: some Stacks
}
sig DataSections, Stacks extends Memory{}

// OS_Object contains memory
sig OS_Object {
	parent : lone OS_App,
	mem: some Memory
}
sig ISRs, Tasks extends OS_Object{}

// OS_Object is including ISRs and Tasks
sig ISRs_1, ISRs_2 {parent : lone ISRs}

// OS_App is including Data section and Stack
sig OS_App {}
sig Trusted_OS, NonTrusted_OS extends OS_App{}

//Mapping
sig AppData {
	values: OS_App -> some Memory 
}

sig ObjData{
	values: OS_Object -> some DataSections
}

//All Memory elements are DataSections or Stack
fact {DataSections + Stacks = Memory}
fact {ISRs + Tasks = OS_Object}
fact {Trusted_OS + NonTrusted_OS = OS_App}

//not null
fact {
	all app:OS_App | some data:DataSections, map:AppData | app -> data in map.values
}

assert difAppDifData{
	all app1, app2: OS_App, data1,data2: DataSections, map:AppData |
	app1 -> data1 in map.values and
	app2 -> data2 in map.values and
	app1 != app2
	implies app1 -> data1 != app2 -> data2
}

assert prf_086{
	all app1:OS_App
}

check difAppDifData
