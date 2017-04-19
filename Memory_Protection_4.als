module mem_pro_4

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
		ownst.belongTo1 = obj

	//Some obj1 and obj2 belong to the same OS_App
	some obj1,obj2: OS_Object, app1: obj1.parent, app2:obj2.parent |
		app1 = app2
	Task + ISR + OS_App = OS_Object
}

//Memory of an applications or object
abstract sig Memory{}

sig DataSections extends Memory{
	belongTo: one OS_Object
}

sig Stacks extends Memory{
	belongTo1: one OS_Object
}

//System status
abstract sig status{}
one sig may_prevent, may_permit, shall_prevent, 
shall_permit extends status{}

abstract sig action{}
one sig read, write extends action{}

//Accesses
sig access{
	from: OS_Object,
	to: Memory,
	per: status,
	act: action
}

sig access1{
	from: OS_App,
	to: Memory,
	per: status,
	act: action
}

//Constraints
//From OS_App to other Objects memory
fact constants_026_086_207_355_356{
	all app1: NonTrusted, app2: OS_App, obj:OS_Object, asc: access1, ds:app2.ownDS, st:obj.ownSt |
		//026
	(
		asc.act = read and
		asc.from = app1 and 
		asc.to = ds and 
		app1 != app2 and
		asc.per = may_prevent
	)
		//086
	or (
		(asc.act = read or asc.act = write) and
		asc.from = app2 and 
		asc.to = app2.ownDS and
		asc.per = shall_permit
	)
		//207
	or (
		asc.act = write and
		asc.from = app1 and 
		asc.to = ds and 
		app1 != app2 and
		asc.per = shall_prevent
	)
		//355
	or (
		asc.act = write and
		asc.from = app1 and
		asc.to = st and
		obj.parent = app2 and
		asc.per = shall_prevent
	)
		//356
	or (
		asc.act = write and
		asc.from = app1 and
		asc.to = ds and
		obj.parent = app2 and
		asc.per = shall_prevent
	)
}

fact constants_196_208_087_195{
	all obj1, obj2: OS_Object, app: NonTrusted, asc: access, st:obj2.ownSt, ds:obj2.ownDS |
	//196
	(
		(obj2 in Task or obj2 in Cate_2) and
		(asc.act = read or asc.act = write) and
		asc.from = obj2 and 
		asc.to = ds and
		asc.per = shall_permit
	)
	//208
	or (
		(obj1 in Task or obj1 in Cate_2) and
		(obj2 in Task or obj2 in Cate_2) and
		obj1.parent = app and
		obj2.parent = app and
		(obj1 != obj2) and
		asc.act = write and
		asc.from = obj1 and
		asc.to = st and
		asc.per = may_prevent
	)
	//087
	or (
		(obj2 in Task or obj2 in Cate_2) and
		(asc.act = read or asc.act = write) and
		asc.from = obj2 and
		asc.to = ds and
		asc.per = shall_permit
	)

	//195
	or (
		(obj1 in Task or obj1 in Cate_2) and
		(obj2 in Task or obj2 in ISR) and
		(obj1.parent = app and obj2.parent = app) and
		obj1 != obj2 and
		asc.act = write and
		asc.from = obj1 and
		asc.to = ds and
		asc.per = may_prevent
	)
		
}


//Events of the system
//From OS_Object to other object
pred run_026[app1: NonTrusted, app2: OS_App, asc: access1, ds:app2.ownDS]{
	asc.act = read and
	asc.from = app1 and
	asc.to = ds and 
	app1 != app2 and
	asc.per = may_prevent
}

pred run_086[app: OS_App, asc: access1]{
	(asc.act = read or asc.act = write) and
	asc.from = app and
	asc.to = app.ownDS and
	asc.per = shall_permit
}

pred run_207[app1: NonTrusted, app2: OS_App, asc: access1, ds:app2.ownDS]{
	asc.act = write and
	asc.from = app1 and 
	asc.to = ds and 
	app1 != app2 and
	asc.per = shall_prevent
}

pred run_196[obj: OS_Object, asc: access]{
	(asc.act = read or asc.act = write) and
	asc.from = obj and
	asc.to = obj.ownSt and
	asc.per = shall_permit
}

pred run_208[app: NonTrusted, obj1,obj2: OS_Object, asc:access, st: obj2.ownSt]{
	(obj1 in Task or obj1 in Cate_2) and
	(obj2 in Task or obj2 in Cate_2) and
	obj1.parent = app and
	obj2.parent = app and
	(obj1 != obj2) and
	asc.act = write and
	asc.from = obj1 and
	asc.to = st and
	asc.per = may_prevent
}

pred run_355[app1: NonTrusted, app2: OS_App, obj:OS_Object , asc: access1, st:obj.ownSt]{
	
	asc.act = write and
	asc.from = app1 and
	asc.to = st and
	obj.parent = app2 and
	asc.per = shall_prevent
}

pred run_087[obj:OS_Object , asc: access, ds:obj.ownDS]{	
	(obj in Task or obj in Cate_2) and
	(asc.act = read or asc.act = write) and
	asc.from = obj and
	asc.to = ds and
	asc.per = shall_permit
}

pred run_195[obj1, obj2: OS_Object, app: NonTrusted, asc: access, ds:obj2.ownDS]{
	(obj1 in Task or obj1 in Cate_2) and
	(obj2 in Task or obj2 in ISR) and
	(obj1.parent = app and obj2.parent = app) and
	obj1 != obj2 and
	asc.act = write and
	asc.from = obj1 and
	asc.to = ds and
	asc.per = may_prevent
}

pred run_356[app1: NonTrusted, app2: OS_App, obj:OS_Object , asc: access1, ds:obj.ownDS]{
	
	asc.act = write and
	asc.from = app1 and
	asc.to = ds and
	obj.parent = app2 and
	asc.per = shall_prevent
}

assert a_208{
	all app: NonTrusted, obj1,obj2: OS_Object, asc:access, st: obj2.ownSt |
//	(obj1 in Task or obj1 in Cate_2) and
	//(obj2 in Task or obj2 in Cate_2) and
	obj1.parent = app and
	obj2.parent = app and
	obj1 != obj2 and
	asc.act = write and
	asc.from = obj1 and
	asc.to = st and
	asc.per = may_prevent
}
check a_208 for 3 but 2 
//run run_026 for 5 but 2 OS_App
//run run_086
//run run_196
//run run_207 for 5 but 2 OS_App
//run run_355 for 5 but 2 OS_App
run run_208 for 5 but 1 OS_App
//run run_195 for 5 
run run_356 for 5 but 2 OS_App
run run_087
