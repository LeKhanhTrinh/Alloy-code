module mem_pro_6

//An object in the operating system
abstract sig OS_Object {
	parent: lone OS_App,
	ownDS: lone DataSections,
	ownSt: lone Stacks
}

//An application in the operating system
sig OS_App extends OS_Object{
	contains: some OS_Object
} {	
	no parent
	lone ownDS
	no ownSt
	}

sig Trusted, NonTrusted extends OS_App {} 

//A Task or ISR
sig Task, ISR extends OS_Object{} {
	one ownDS
	one ownSt
}
sig Cate_1, Cate_2 extends ISR{}

/*An OS_App is the parent of what is contained
All Objects are OS_App, Tasks, and ISR
*/
fact{
	//An OS_Object is the parent of what is contained
	all app: OS_App, cont: app.contains |
		cont.parent = app
	all obj: OS_Object,  ownds: obj.ownDS |
		ownds.belongTo = obj
	all obj: OS_Object,  ownst: obj.ownSt |
		ownst.belongTo = obj

	Task + ISR + OS_App = OS_Object
}

//Memory of an applications or object
abstract sig Memory{}

sig DataSections, Stacks extends Memory{
	belongTo: one OS_Object
}


//System status

abstract sig status{
}

sig access{
	from: OS_Object,
	to: Memory,
	act: action
}

//mapping
sig permission{
	per: access -> lone status
}

one sig may_prevent, may_permit, shall_prevent, 
shall_permit extends status{}

abstract sig action{}
one sig read, write extends action{}


fact constants_026_086_207_355_356{
	//026 and 207
	all s: status, app1:NonTrusted, app2: OS_App, ds: app2.ownDS |
		s.from = app1 and
		s.to = ds and
		(s.act = read or s.act = write)
		implies s in may_prevent

	//086
	
}


fun P_026[app1: NonTrusted, app2: OS_App, pr: permission, ds:app2.ownDS]:{
	status.(pr.per)
}

assert A_026_207{
	all app1: NonTrusted, app2: OS_App, stt1, stt2: status, ds:app2.ownDS |
		stt1 in P_026[app1, app2, may_prevent] and
		stt2 in P_207[app1, app2, may_prevent]
}

/*
pred P_026[app1: NonTrusted, app2: OS_App, stt: status, ds:app2.ownDS] {
	stt.from = app1 and
	stt.to = ds and
	stt.act = read implies
	stt = may_prevent
}

pred P_207[app1: NonTrusted, app2: OS_App, stt: status, ds:app2.ownDS] {
	stt.from = app1 and
	stt.to = ds and
	stt.act = write implies
	stt = may_prevent
}


assert A_026_207{
	all app1: NonTrusted, app2: OS_App, stt1, stt2: status, ds:app2.ownDS |
		stt1 in P_026[app1, app2, may_prevent] and
		stt2 in P_207[app1, app2, may_prevent]
}
*/
check  A_026_207
