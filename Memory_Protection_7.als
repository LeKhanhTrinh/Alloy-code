module mem_pro_7

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
	//OS_Object including Tasks, ISRs, and OS_Apps
	Task + ISR + OS_App = OS_Object
}

//Memory of an applications or object
abstract sig Memory{}

sig DataSections, Stacks extends Memory{
	belongTo: one OS_Object
}

//System status
abstract sig Status{}
one sig May_Prevent, May_Permit, Shall_Prevent,  Shall_Permit extends Status{}

abstract sig Action{}
one sig Read, Write extends Action{}

//The Request Access to Memory
sig Request{
	from: OS_Object,
	to: Memory,
	act: Action,
	per: Request -> Status
}


// ------------------------------------------------------------------------------------------------------------------------
// 026_086_207_355_356
fact constraint_set{
	//026
	all req: Request, app1: NonTrusted, app2: OS_App, ds: app2.ownDS | 
		P_026[req, app1, app2, ds] implies req.per[Request] = May_Prevent

	//086
	all req: Request, app: OS_App, ds: app.ownDS | 
		P_086[req, app, ds] implies req.per[Request] = Shall_Permit

	//207
	all req: Request, app1: NonTrusted, app2: OS_App, ds: app2.ownDS | 
		P_207[req, app1, app2, ds] implies req.per[Request] = Shall_Prevent

	//196
	all req: Request, obj: OS_Object, st: obj.ownSt | 
		P_196[req, obj, st] implies req.per[Request] = Shall_Permit

	//208
	all req: Request, app: NonTrusted, obj1, obj2: OS_Object, st: obj2.ownSt | 
		P_208[req, app, obj1, obj2, st] implies req.per[Request] = May_Prevent

	//355
	all req: Request, app: NonTrusted, obj: OS_Object, st: obj.ownSt | 
		P_355[req, app, obj, st] implies req.per[Request] = Shall_Prevent

	//196
	all req: Request, obj: OS_Object, ds: obj.ownDS | 
		P_087[req, obj, ds] implies req.per[Request] = Shall_Permit

	//195
	all req: Request, app: NonTrusted, obj1, obj2: OS_Object, ds: obj2.ownDS | 
		P_195[req, app, obj1, obj2, ds] implies req.per[Request] = May_Prevent

	//356
	all req: Request, app1: NonTrusted, app2: OS_App, ds: app2.ownDS | 
		P_356[req, app1, app2, ds] implies req.per[Request] = Shall_Prevent
}

// ------------------------------------------------------------------------------------------------------------------------
// 026
//Assign a request 
pred P_026 [req: Request, app1: NonTrusted, app2: OS_App, ds: app2.ownDS]{
	req.from = app1
	req.to = ds
	req.act = Read
}

// 086
//Assign a request 
pred P_086 [req: Request, app: OS_App, ds: app.ownDS]{
	(req.act = Read or req.act = Write) 
	req.from = app  
	req.to = ds 
}

// 207
//Assign a request 
pred P_207 [req: Request, app1: NonTrusted, app2: OS_App, ds: app2.ownDS]{
	req.from = app1
	req.to = ds
	req.act = Write
}

// 196
//Assign a request 
pred P_196 [req: Request, obj: OS_Object, st: obj.ownSt]{
	(req.act = Read or req.act = Write) 
	req.from = obj  
	req.to = st 
}

// 208
//Assign a request 
pred P_208 [req: Request, app: NonTrusted, obj1, obj2: OS_Object, st: obj2.ownSt]{
	(obj1 in Task or obj1 in Cate_2) 
	(obj2 in Task or obj2 in Cate_2) 
	obj1.parent = app 
	obj2.parent = app 
	(obj1 != obj2) 
	req.act = Write 
	req.from = obj1 
	req.to = st  
}

// 355
//Assign a request 
pred P_355 [req: Request, app: NonTrusted, obj: OS_Object, st: obj.ownSt]{
	obj.parent = OS_App
	app != obj.parent
	req.act = Write
	req.from = app
	req.to = st
}

// 087
//Assign a request 
pred P_087 [req: Request, obj: OS_Object, ds: obj.ownDS]{
	(req.act = Read or req.act = Write) 
	req.from = obj  
	req.to = ds 
}

// 195
//Assign a request 
pred P_195 [req: Request, app: NonTrusted, obj1, obj2: OS_Object, ds: obj2.ownDS]{
	(obj1 in Task or obj1 in Cate_2) 
	(obj2 in Task or obj2 in Cate_2) 
	obj1.parent = app 
	obj2.parent = app 
	(obj1 != obj2) 
	(req.act = Write or req.act = Read)
	req.from = obj1 
	req.to = ds  
}

// 356
//Assign a request 
pred P_356 [req: Request, app1: NonTrusted, app2: OS_App, ds: app2.ownDS]{
	req.from = app1
	req.to = ds
	req.act = Write
}

// ------------------------------------------------------------------------------------------------------------------------
//Assertions
assert C_026_086{
	all req026, req086: Request, app1: NonTrusted, app2: OS_App, ds: app2.ownDS |
		P_026[req026, app1, app2, ds] and 
		P_086[req086,app2,ds] and 
		req026.per[Request] != req086.per[Request]
}

//207
assert C_207_086{
	all req207, req086: Request, app1: NonTrusted, app2: OS_App, ds: app2.ownDS |
		P_207[req207, app1, app2, ds] and P_086[req086,app2,ds] and req207.per[Request] != req086.per[Request]
}

assert C_207_026{
	all req207, req026: Request, app1: NonTrusted, app2: OS_App, ds: app2.ownDS |
		P_207[req207, app1, app2, ds] and P_026[req026, app1, app2, ds] and req207.per[Request] != req026.per[Request]
}

//196
assert C_196_086{
	all req196, req086: Request, obj: OS_Object, app: OS_App, ds: app.ownDS, st: obj.ownSt |
		P_196[req196, obj, st] and P_086[req086,app,ds] and req196.per[Request] != req086.per[Request]
}

assert C_196_026{
	all req196, req026: Request, app1: NonTrusted, app2: OS_App, ds: app2.ownDS, obj:OS_Object, st:obj.ownSt |
		P_196[req196, obj, st] and P_026[req026, app1, app2, ds] and req196.per[Request] != req026.per[Request]
}

assert C_196_207{
	all req196, req207: Request, app1: NonTrusted, app2: OS_App, ds: app2.ownDS, obj:OS_Object, st:obj.ownSt |
		P_196[req196, obj, st] and P_207[req207, app1, app2, ds] and req196.per[Request] != req207.per[Request]
}

//208
assert C_208_086{
	all req208, req086: Request, app1: NonTrusted, app: OS_App, ds: app.ownDS, obj1, obj2:OS_Object, st:obj2.ownSt |
		P_208[req208, app1, obj1, obj2, st] and P_086[req086,app,ds] and req208.per[Request] != req086.per[Request]
}

assert C_208_026{
	all req208, req026: Request, app1: NonTrusted, app2: OS_App, ds: app2.ownDS, obj1, obj2:OS_Object, st:obj2.ownSt |
		P_208[req208, app1, obj1, obj2, st] and P_026[req026, app1, app2, ds] and req208.per[Request] != req026.per[Request]
}

assert C_208_207{
	all req208, req207: Request, app1: NonTrusted, app2: OS_App, ds: app2.ownDS, obj1, obj2:OS_Object, st:obj2.ownSt |
		P_208[req208, app1, obj1, obj2, st] and P_207[req207, app1, app2, ds] and req208.per[Request] != req207.per[Request]
}

assert C_208_196{
	all req208, req196: Request, app1: NonTrusted, obj1, obj2:OS_Object, st:obj2.ownSt |
		P_208[req208, app1, obj1, obj2, st] and P_196[req196, obj2, st] and req208.per[Request] != req196.per[Request]
}

//355
assert C_355_086{
	all req355, req086: Request, app1: NonTrusted, app: OS_App, ds: app.ownDS, obj:OS_Object, st:obj.ownSt |
		P_355[req355, app1, obj, st] and P_086[req086,app,ds] and req355.per[Request] != req086.per[Request]
}

assert C_355_026{
	all req355, req026: Request, app1: NonTrusted, app2: OS_App, ds: app2.ownDS, obj:OS_Object, st:obj.ownSt |
		P_355[req355, app1, obj, st] and P_026[req026, app1, app2, ds] and req355.per[Request] != req026.per[Request]
}

assert C_355_207{
	all req355, req207: Request, app1: NonTrusted, app2: OS_App, ds: app2.ownDS, obj:OS_Object, st:obj.ownSt |
		P_355[req355, app1, obj, st] and P_207[req207, app1, app2, ds] and req355.per[Request] != req207.per[Request]
}

assert C_355_196{
	no req355, req196: Request, app1: NonTrusted, obj1, obj2:OS_Object, st:obj2.ownSt, st1:obj1.ownSt  |
		P_355[req355, app1, obj1, st1] and P_196[req196, obj2, st] and req355.per[Request] != req196.per[Request]
}

assert C_355_208{
	all req355, req208: Request, app1: NonTrusted, obj, obj1, obj2:OS_Object, st: obj.ownSt, st1:obj2.ownSt  |
		P_355[req355, app1, obj, st] and P_208[req208, app1, obj1, obj2, st1] and req355.per[Request] != req208.per[Request]
}

//087
assert C_087_086{
	all req087, req086: Request, app: OS_App, ds: app.ownDS, obj:OS_Object, ds1:obj.ownDS |
		P_087[req087, obj, ds1] and P_086[req086,app,ds] and req087.per[Request] != req086.per[Request]
}

assert C_087_026{
	all req087, req026: Request, app1: NonTrusted, app2: OS_App, ds: app2.ownDS, obj:OS_Object, ds1:obj.ownDS |
		P_087[req087, obj, ds1] and P_026[req026, app1, app2, ds] and req087.per[Request] != req026.per[Request]
}

assert C_087_207{
	all req087, req207: Request, app1: NonTrusted, app2: OS_App, ds: app2.ownDS, obj:OS_Object, ds1:obj.ownDS |
		P_087[req087, obj, ds1] and P_207[req207, app1, app2, ds] and req087.per[Request] != req207.per[Request]
}

assert C_087_196{
	all req087, req196: Request, obj:OS_Object, st:obj.ownSt, ds:obj.ownDS  |
		P_087[req087, obj, ds] and P_196[req196, obj, st] and req087.per[Request] != req196.per[Request]
}

assert C_087_208{
	all req087, req208: Request, app1: NonTrusted, obj, obj1, obj2:OS_Object, st: obj2.ownSt, ds:obj.ownDS  |
		P_087[req087, obj, ds] and P_208[req208, app1, obj1, obj2, st] and req087.per[Request] != req208.per[Request]
}

assert C_087_355{
	all req087, req355: Request, app1: NonTrusted, obj, obj1:OS_Object, st: obj1.ownSt, ds:obj.ownDS  |
		P_087[req087, obj, ds] and P_355[req355, app1, obj1, st] and req087.per[Request] != req355.per[Request]
}

//195
assert C_195_086{
	no req195, req086: Request, app: OS_App, app1: NonTrusted, ds: app.ownDS, obj1, obj2:OS_Object, ds1:obj2.ownDS |
		P_195[req195, app1, obj1, obj2, ds1] and P_086[req086,app,ds] and req195.per[Request] != req086.per[Request]
}

assert C_195_026{
	no req195, req026: Request, app1: NonTrusted, app2: OS_App, ds: app2.ownDS, obj1, obj2:OS_Object, ds1:obj2.ownDS |
		P_195[req195, app1, obj1, obj2, ds1] and P_026[req026, app1, app2, ds] and req195.per[Request] != req026.per[Request]
}

assert C_195_207{
	no req195, req207: Request, app1: NonTrusted, app2: OS_App, ds: app2.ownDS, obj1, obj2:OS_Object, ds1:obj2.ownDS |
		P_195[req195, app1, obj1, obj2, ds1] and P_207[req207, app1, app2, ds] and req195.per[Request] != req207.per[Request]
}

assert C_195_196{
	no req195, req196: Request, app1: NonTrusted, obj, obj1, obj2:OS_Object, st:obj.ownSt, ds:obj2.ownDS  |
		P_195[req195, app1, obj1, obj2, ds] and P_196[req196, obj, st] and req195.per[Request] != req196.per[Request]
}

assert C_195_208{
	no req195, req208: Request, app1: NonTrusted, obj1, obj2:OS_Object, st: obj2.ownSt, ds:obj2.ownDS  |
		P_195[req195, app1, obj1, obj2, ds] and P_208[req208, app1, obj1, obj2, st] and req195.per[Request] != req208.per[Request]
}

assert C_195_355{
	no req195, req355: Request, app1: NonTrusted, obj1, obj2:OS_Object, st: obj1.ownSt, ds:obj2.ownDS  |
		P_195[req195, app1, obj1, obj2, ds] and P_355[req355, app1, obj1, st] and req195.per[Request] != req355.per[Request]
}

assert C_195_087{
	no req087, req195: Request, app1: NonTrusted, obj, obj1, obj2:OS_Object, ds1: obj2.ownDS, ds:obj.ownDS  |
		P_087[req087, obj, ds] and P_195[req195, app1, obj1, obj2, ds1] and req087.per[Request] != req195.per[Request]
}

//356
assert C_356_086{
	no req356, req086: Request, app: OS_App, app1: NonTrusted, ds: app.ownDS|
		P_356[req356, app1, app, ds] and 
		P_086[req086,app,ds] and 
		req356.per[Request] != req086.per[Request]
}

assert C_356_026{
	no req356, req026: Request, app1: NonTrusted, app2: OS_App, ds: app2.ownDS |
		P_356[req356, app1, app2, ds] and P_026[req026, app1, app2, ds] and req356.per[Request] != req026.per[Request]
}

assert C_356_207{
	no req356, req207: Request, app1: NonTrusted, app2: OS_App, ds: app2.ownDS |
		P_356[req356, app1, app2, ds] and P_207[req207, app1, app2, ds] and req356.per[Request] != req207.per[Request]
}

assert C_356_196{
	no req356, req196: Request, app1: NonTrusted, app2: OS_App, obj :OS_Object, st:obj.ownSt, ds:app2.ownDS  |
		P_356[req356, app1, app2, ds] and P_196[req196, obj, st] and req356.per[Request] != req196.per[Request]
}

assert C_356_208{
	no req356, req208: Request, app1: NonTrusted, app2: OS_App, obj1, obj2:OS_Object, st: obj2.ownSt, ds:app2.ownDS  |
		P_356[req356, app1, app2, ds] and P_208[req208, app1, obj1, obj2, st] and req356.per[Request] != req208.per[Request]
}

assert C_356_355{
	no req356, req355: Request, app1: NonTrusted, app2:OS_App, obj1:OS_Object, st: obj1.ownSt, ds:app2.ownDS  |
		P_356[req356, app1, app2, ds] and P_355[req355, app1, obj1, st] and req356.per[Request] != req355.per[Request]
}

assert C_356_087{
	no req087, req356: Request, app1: NonTrusted, app2: OS_App, obj:OS_Object, ds1: app2.ownDS, ds:obj.ownDS  |
		P_087[req087, obj, ds] and P_356[req356, app1, app2, ds1] and req087.per[Request] != req356.per[Request]
}

assert C_356_195{
	no req195, req356: Request, app1: NonTrusted, app2: OS_App, ds: app2.ownDS, obj1, obj2:OS_Object, ds1:obj2.ownDS |
		P_195[req195, app1, obj1, obj2, ds1] and P_356[req356, app1, app2, ds] and req195.per[Request] != req356.per[Request]
}
// ------------------------------------------------------------------------------------------------------------------------
//Check Assertions
check C_356_195
check C_356_087
check C_356_355
check C_356_208
check C_356_196
check C_356_207
check C_356_026
check C_356_086
check C_195_087
check C_195_355
check C_195_208
check C_195_196
check C_195_207
check C_195_026
check C_195_086
check C_087_355
check C_087_208
check C_087_196
check C_087_207
check C_087_026
check C_087_086
check C_355_208
check C_355_196
check C_355_207
check C_355_026
check C_355_086
check C_208_196
check C_208_207
check C_208_026
check C_208_086
check C_196_207
check C_196_086
check C_196_026
check C_207_026
check C_207_086
check C_026_086
