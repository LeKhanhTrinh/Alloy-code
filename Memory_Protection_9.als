module mem_pro_9

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

	//no need to share stack
	//all obj1, obj2: OS_Object |
	//	obj1.ownSt != obj2.ownSt

	//Gen1: From obj to the App.data
	all req: Request, app: OS_App, obj: OS_Object | 
		P_SameApp[req, app, obj] and req.per[Request] = Shall_Permit

	//Gen2: From obj to the App2.data
	all req: Request, app1, app2: OS_App, obj: OS_Object | 
		P_DiffApp[req, app1, app2, obj] and req.per[Request] = Shall_Prevent

	//Gen3: From app to obj.stack
	all req: Request, app: OS_App, obj: OS_Object | 
		P_GenStack[req, app, obj] implies req.per[Request] = May_Permit

	//Gen4: From app to obj.data
	all req: Request, app: OS_App, obj: OS_Object | 
		P_GenData[req, app, obj] implies req.per[Request] = May_Permit

	//Gen5: From obj1 to obj2 stack
	all req: Request, app: OS_App, obj1, obj2: OS_Object | 
		P_GenStack2[req, app, obj1, obj2] and req.per[Request] = Shall_Prevent
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

one sig Start{
	empty: one OS_App
}

// ------------------------------------------------------------------------------------------------------------------------
// 026_086_207_355_356
fact constraint_set{
	//026: From App1 to App2's DS
	all req: Request, app1: NonTrusted, app2: OS_App | 
		P_026[req, app1, app2] implies req.per[Request] = May_Prevent

	//086: From App to App's Data
	all req: Request, app: OS_App| 
		P_086[req, app] implies req.per[Request] = Shall_Permit

	//207: From App1 to App2's DS
	all req: Request, app1: NonTrusted, app2: OS_App | 
		P_207[req, app1, app2] implies req.per[Request] = Shall_Prevent



	//----------------------------------------------------------------------------------------------------------------
	//196: From Obj to Obj's Stack
	all req: Request, obj: OS_Object| 
		P_196[req, obj] implies req.per[Request] = Shall_Permit

	//208: from Obj1 to Obj2's Stack
	all req: Request, app: NonTrusted, obj1, obj2: OS_Object | 
		P_208[req, app, obj1, obj2] implies req.per[Request] = May_Prevent

	//355: from App to App2.obj.Stack
	all req: Request, app: NonTrusted, obj: OS_Object| 
		P_355[req, app, obj] implies req.per[Request] = Shall_Prevent
	

	


	//----------------------------------------------------------------------------------------------------------------
	//087: From Obj to Obj.Ds
	all req: Request, obj: OS_Object | 
		P_087[req, obj] implies req.per[Request] = Shall_Permit

	//195: From app.obj1 to app.obj2.DS
	all req: Request, app: NonTrusted, obj1, obj2: OS_Object| 
		P_195[req, app, obj1, obj2] implies req.per[Request] = May_Prevent

	//356: From app1 to app2.DS
	all req: Request, app1: NonTrusted, app2: OS_App| 
		P_356[req, app1, app2] implies req.per[Request] = Shall_Prevent

}

fact OSConstruction { 
   OS_App in (Start.empty).*{x: OS_App, y: x.contains} 
} 

//Private data of an OS-APP
//-----------------------------------------------------------------------------------------------------------------------------------
// 086
//R&W: From App to App's Data
pred P_086 [req: Request, app: OS_App]{
	(req.act = Read or req.act = Write) 
	req.from = app  
	req.to = app.ownDS 
}
// 207
//W: From App1 to App2's DS
pred P_207 [req: Request, app1: NonTrusted, app2: OS_App]{
	req.from = app1
	req.to = app2.ownDS
	req.act = Write
}
// 026
//R: From App1 to App2's DS
pred P_026 [req: Request, app1: NonTrusted, app2: OS_App]{
	req.from = app1
	req.to = app2.ownDS
	req.act = Read
}

//gen1
//R&W: From obj to the App.data
pred P_SameApp[req: Request, app: OS_App, obj: OS_Object]{
	obj.parent = app
	req.from = obj
	req.to = app.ownDS
	(req.act = Read or req.act = Write)
}

//gen2
pred P_DiffApp[req: Request, app1, app2: OS_App, obj: OS_Object]{
	obj.parent = app1
	req.from = obj
	req.to = app2.ownDS
	(req.act = Read or req.act = Write)
}

//Private stack of an Os Object
//-----------------------------------------------------------------------------------------------------------------------------------
//gen3
//R&W: From app to obj.stack
pred P_GenStack[req: Request, app: OS_App, obj: OS_Object]{
	req.from = app
	obj.parent = app
	req.to = obj.ownSt
	(req.act = Read or req.act  = Write)
}

//196
//R&W: From Obj to Obj's Stack
pred P_196 [req: Request, obj: OS_Object]{
	(req.act = Read or req.act = Write) 
	req.from = obj  
	req.to = obj.ownSt 
}
// 208
//W: from Obj1 to Obj2's Stack
pred P_208 [req: Request, app: NonTrusted, obj1, obj2: OS_Object]{
	(obj1 in Task or obj1 in Cate_2) 
	(obj2 in Task or obj2 in Cate_2) 
	obj1.parent = app 
	obj2.parent = app 
	(obj1 != obj2) 
	req.act = Write 
	req.from = obj1 
	req.to = obj2.ownSt  
}
// 355
//W: from App to App2.obj.Stack
pred P_355 [req: Request, app: NonTrusted, obj: OS_Object]{
	obj.parent = OS_App
	app != obj.parent
	req.act = Write
	req.from = app
	req.to = obj.ownSt
}

// 208
//W: from Obj1 to Obj2's Stack
pred P_GenStack2 [req: Request, app: OS_App, obj1, obj2: OS_Object]{
	(obj1 in Task or obj1 in Cate_2) 
	(obj2 in Task or obj2 in Cate_2) 
	obj1.parent = app 
	obj2.parent = app 
	(obj1 != obj2) 
	(req.act = Write or req.act = Read)
	req.from = obj1 
	req.to = obj2.ownSt  
}

//Private data of an Os Object
//-----------------------------------------------------------------------------------------------------------------------------------
//gen4
//R&W: From app to obj.data
pred P_GenData[req: Request, app: OS_App, obj: OS_Object]{
	req.from = app
	obj.parent = app
	req.to = obj.ownDS
	(req.act = Read or req.act  = Write)
}

// 087
//R&W: From Obj to Obj.Ds
pred P_087 [req: Request, obj: OS_Object]{
	(req.act = Read or req.act = Write) 
	req.from = obj  
	req.to = obj.ownDS 
}

// 195
//R&W: From app.obj1 to app.obj2.DS
pred P_195 [req: Request, app: NonTrusted, obj1, obj2: OS_Object]{
	(obj1 in Task or obj1 in Cate_2) 
	(obj2 in Task or obj2 in Cate_2) 
	obj1.parent = app 
	obj2.parent = app 
	(obj1 != obj2) 
	(req.act = Write or req.act = Read)
	req.from = obj1 
	req.to = obj2.ownDS  
}
// 356
//W: From app1 to app2.DS
pred P_356 [req: Request, app1: NonTrusted, app2: OS_App]{
	req.from = app1
	req.to = app2.ownDS
	req.act = Write
}

////-----------------------------------------------------------------------------------------------------------------------------------
//Assertions
assert C_026_086{
	all req026, req086: Request, app1: NonTrusted, app2: OS_App|
		P_026[req026, app1, app2] and 
		P_086[req086,app2] and 
		req026.per[Request] != req086.per[Request]
}

//207
assert C_207_086{
	all req207, req086: Request, app1: NonTrusted, app2: OS_App |
		P_207[req207, app1, app2] and 
		P_086[req086,app2] and 
		req207.per[Request] != req086.per[Request]
}

assert C_207_026{
	all req207, req026: Request, app1: NonTrusted, app2: OS_App|
		P_207[req207, app1, app2] and 
		P_026[req026, app1, app2] and 
		req207.per[Request] != req026.per[Request]
}

//Same App
assert C_SameApp_026{
	all reqSA, req026: Request, app1: NonTrusted, app2: OS_App, obj: OS_Object|
		P_SameApp[reqSA, app2, obj] and
		P_026[req026, app1, app2] and
		reqSA.per[Request] != req026.per[Request]
}

assert C_SameApp_086{
	all reqSA, req086: Request, app: OS_App, obj: OS_Object|
		P_SameApp[reqSA, app, obj] and
		P_086[req086, app] and
		reqSA.per[Request] != req086.per[Request]
}

assert C_SameApp_207{
	all reqSA, req207: Request, app1: NonTrusted, app2: OS_App, obj: OS_Object|
		P_SameApp[reqSA, app2, obj] and
		P_207[req207, app1, app2] and
		reqSA.per[Request] != req207.per[Request]
}

// Different App
assert C_DiffApp_026{
	all reqDA, req026: Request, app1: NonTrusted, app2: OS_App, obj: OS_Object|
		P_DiffApp[reqDA, app1, app2, obj] and
		P_026[req026, app1, app2] and
		reqDA.per[Request] != req026.per[Request]
}

assert C_DiffApp_086{
	all reqDA, req086: Request, app1: NonTrusted, app2: OS_App, obj: OS_Object|
		P_DiffApp[reqDA, app1, app2, obj] and
		P_086[req086, app2] and
		reqDA.per[Request] != req086.per[Request]
}

assert C_DiffApp_207{
	all reqDA, req207: Request, app1: NonTrusted, app2: OS_App, obj: OS_Object|
		P_DiffApp[reqDA, app1, app2, obj] and
		P_207[req207, app1, app2] and
		reqDA.per[Request] != req207.per[Request]
}

assert C_DiffApp_SameApp{
	all reqDA, reqSA: Request, app1: NonTrusted, app2: OS_App, obj: OS_Object|
		P_DiffApp[reqDA, app1, app2, obj] and
		P_SameApp[reqSA, app2, obj] and
		reqDA.per[Request] != reqSA.per[Request]
}

//196
assert C_196_086{
	all req196, req086: Request, obj: OS_Object, app: OS_App|
		P_196[req196, obj] and 
		P_086[req086,app] and 
		req196.per[Request] != req086.per[Request]
}

assert C_196_026{
	all req196, req026: Request, app1: NonTrusted, app2: OS_App, obj:OS_Object|
		P_196[req196, obj] and 
		P_026[req026, app1, app2] and 
		req196.per[Request] != req026.per[Request]
}

assert C_196_207{
	all req196, req207: Request, app1: NonTrusted, app2: OS_App, obj:OS_Object |
		P_196[req196, obj] and 
		P_207[req207, app1, app2] and 
		req196.per[Request] != req207.per[Request]
}

assert C_196_DiffApp{
	all req196, reqDA: Request, app1: NonTrusted, app2: OS_App, obj:OS_Object |
		P_196[req196, obj] and 
		P_DiffApp[reqDA, app1, app2, obj] and 
		req196.per[Request] != reqDA.per[Request]

}

assert C_196_SameApp{
	all req196, reqSA: Request, obj: OS_Object, app: OS_App|
		P_196[req196, obj] and 
		P_SameApp[reqSA,app, obj] and 
		req196.per[Request] != reqSA.per[Request]
}

//208
assert C_208_086{
	all req208, req086: Request, app1: NonTrusted, app: OS_App, obj1, obj2:OS_Object|
		P_208[req208, app1, obj1, obj2] and
		P_086[req086,app] and 
		req208.per[Request] != req086.per[Request]
}

assert C_208_026{
	all req208, req026: Request, app1: NonTrusted, app2: OS_App, obj1, obj2:OS_Object|
		P_208[req208, app1, obj1, obj2] and 
		P_026[req026, app1, app2] and 
		req208.per[Request] != req026.per[Request]
}

assert C_208_207{
	all req208, req207: Request, app1: NonTrusted, app2: OS_App, obj1, obj2:OS_Object |
		P_208[req208, app1, obj1, obj2] and 
		P_207[req207, app1, app2] and 
		req208.per[Request] != req207.per[Request]
}

assert C_208_196{
	all req208, req196: Request, app1: NonTrusted, obj1, obj2:OS_Object|
		P_208[req208, app1, obj1, obj2] and 
		P_196[req196, obj2] and 
		req208.per[Request] != req196.per[Request]
}

assert C_208_SameApp{
	all req208, reqSA: Request, app1: NonTrusted, app: OS_App, obj1, obj2:OS_Object|
		P_208[req208, app1, obj1, obj2] and
		P_SameApp[reqSA,app, obj1] and 
		req208.per[Request] != reqSA.per[Request]
}

assert C_208_DiffApp{
	all req208, reqDA: Request, app1: NonTrusted, app: OS_App, obj1, obj2:OS_Object|
		P_208[req208, app1, obj1, obj2] and
		P_DiffApp[reqDA, app1, app, obj1] and 
		req208.per[Request] != reqDA.per[Request]
}

//355
assert C_355_086{
	all req355, req086: Request, app1: NonTrusted, app: OS_App, obj:OS_Object |
		P_355[req355, app1, obj] and 
		P_086[req086,app] and 
		req355.per[Request] != req086.per[Request]
}

assert C_355_026{
	all req355, req026: Request, app1: NonTrusted, app2: OS_App, obj:OS_Object|
		P_355[req355, app1, obj] and 
		P_026[req026, app1, app2] and 
		req355.per[Request] != req026.per[Request]
}

assert C_355_207{
	all req355, req207: Request, app1: NonTrusted, app2: OS_App, obj:OS_Object |
		P_355[req355, app1, obj] and 
		P_207[req207, app1, app2] and 
		req355.per[Request] != req207.per[Request]
}

assert C_355_196{
	all req355, req196: Request, app1: NonTrusted, obj1, obj2:OS_Object  |
		P_355[req355, app1, obj1] and 
		P_196[req196, obj2] and 
		req355.per[Request] != req196.per[Request]
}

assert C_355_208{
	all req355, req208: Request, app1: NonTrusted, obj, obj1, obj2:OS_Object |
		P_355[req355, app1, obj] and 
		P_208[req208, app1, obj1, obj2] and 
		req355.per[Request] != req208.per[Request]
}

assert C_355_SameApp{
	all req355, reqSA: Request, app1: NonTrusted, app: OS_App, obj, obj1:OS_Object |
		P_355[req355, app1, obj] and 
		P_SameApp[reqSA,app, obj1] and 
		req355.per[Request] != reqSA.per[Request]
}

assert C_355_DiffApp{
	all req355, reqDA: Request, app1: NonTrusted, app: OS_App, obj, obj1:OS_Object |
		P_355[req355, app1, obj] and 
		P_DiffApp[reqDA,app1, app, obj1] and 
		req355.per[Request] != reqDA.per[Request]
}

//GenStack
assert C_GenStack_086{
	all reqGS, req086: Request, app2: OS_App, obj2:OS_Object |
		P_GenStack[reqGS, app2, obj2] and 
		P_086[req086,app2] and 
		reqGS.per[Request] != req086.per[Request]
}

assert C_GenStack_026{
	all reqGS, req026: Request, app1: NonTrusted, app2: OS_App, obj2:OS_Object |
		P_GenStack[reqGS, app2, obj2] and 
		P_026[req026, app1, app2] and 
		reqGS.per[Request] != req026.per[Request]
}

assert C_GenStack_207{
	all reqGS, req207: Request, app1: NonTrusted, app2: OS_App, obj:OS_Object |
		P_GenStack[reqGS, app2, obj] and 
		P_207[req207, app1, app2] and 
		reqGS.per[Request] != req207.per[Request]
}

assert C_GenStack_196{
	all reqGS, req196: Request, app2: OS_App, obj1, obj2:OS_Object  |
		P_GenStack[reqGS, app2, obj1] and 
		P_196[req196, obj2] and 
		reqGS.per[Request] != req196.per[Request]
}

assert C_GenStack_208{
	all reqGS, req208: Request, app1: NonTrusted, app2: OS_App, obj, obj1, obj2:OS_Object |
		P_GenStack[reqGS, app2, obj] and 
		P_208[req208, app1, obj1, obj2] and 
		reqGS.per[Request] != req208.per[Request]
}

assert C_GenStack_SameApp{
	all reqGS, reqSA: Request, app: OS_App, obj, obj1:OS_Object |
		P_GenStack[reqGS, app, obj] and 
		P_SameApp[reqSA, app, obj1] and 
		reqGS.per[Request] != reqSA.per[Request]
}

assert C_GenStack_DiffApp{
	all reqGS, reqDA: Request, app1: NonTrusted, app2: OS_App, obj, obj1:OS_Object |
		P_GenStack[reqGS, app2, obj] and 
		P_DiffApp[reqDA,app1, app2, obj1] and 
		reqGS.per[Request] != reqDA.per[Request]
}

assert C_GenStack_355{
	all reqGS, req355: Request, app1: NonTrusted, app2: OS_App, obj, obj1:OS_Object |
		P_GenStack[reqGS, app2, obj] and 
		P_355[req355,app1, obj1] and 
		reqGS.per[Request] != req355.per[Request]
}

//087
assert C_087_086{
	all req087, req086: Request, app: OS_App, obj:OS_Object |
		P_087[req087, obj] and 
		P_086[req086,app] and 
		req087.per[Request] != req086.per[Request]
}

assert C_087_026{
	all req087, req026: Request, app1: NonTrusted, app2: OS_App, obj:OS_Object|
		P_087[req087, obj] and 
		P_026[req026, app1, app2] and 
		req087.per[Request] != req026.per[Request]
}

assert C_087_207{
	all req087, req207: Request, app1: NonTrusted, app2: OS_App, obj:OS_Object|
		P_087[req087, obj] and 
		P_207[req207, app1, app2] and 
		req087.per[Request] != req207.per[Request]
}

assert C_087_196{
	all req087, req196: Request, obj:OS_Object  |
		P_087[req087, obj] and 
		P_196[req196, obj] and 
		req087.per[Request] != req196.per[Request]
}

assert C_087_208{
	all req087, req208: Request, app1: NonTrusted, obj, obj1, obj2:OS_Object |
		P_087[req087, obj] and 
		P_208[req208, app1, obj1, obj2] and
		req087.per[Request] != req208.per[Request]
}

assert C_087_355{
	all req087, req355: Request, app1: NonTrusted, obj, obj1:OS_Object |
		P_087[req087, obj] and 
		P_355[req355, app1, obj1] and 
		req087.per[Request] != req355.per[Request]
}

assert C_087_SameApp{
	all req087, reqSA: Request, app2: OS_App, obj, obj1:OS_Object |
		P_087[req087, obj] and 
		P_SameApp[reqSA, app2, obj1] and 
		req087.per[Request] != reqSA.per[Request]
}

assert C_087_DiffApp{
	all req087, reqDA: Request, app1: NonTrusted, app2: OS_App, obj, obj1:OS_Object |
		P_087[req087, obj] and 
		P_DiffApp[reqDA, app1, app2, obj1] and 
		req087.per[Request] != reqDA.per[Request]
}

assert C_087_GenStack{
	all req087, reqGS: Request, app2: OS_App, obj, obj1:OS_Object |
		P_087[req087, obj] and 
		P_GenStack[reqGS, app2, obj1] and 
		req087.per[Request] != reqGS.per[Request]
}

//195
assert C_195_086{
	all req195, req086: Request, app: OS_App, app1: NonTrusted, obj1, obj2:OS_Object |
		P_195[req195, app1, obj1, obj2] and 
		P_086[req086,app] and 
		req195.per[Request] != req086.per[Request]
}

assert C_195_026{
	all req195, req026: Request, app1: NonTrusted, app2: OS_App, obj1, obj2:OS_Object |
		P_195[req195, app1, obj1, obj2] and 
		P_026[req026, app1, app2] and 
		req195.per[Request] != req026.per[Request]
}

assert C_195_207{
	all req195, req207: Request, app1: NonTrusted, app2: OS_App, obj1, obj2:OS_Object |
		P_195[req195, app1, obj1, obj2] and 
		P_207[req207, app1, app2] and 
		req195.per[Request] != req207.per[Request]
}

assert C_195_196{
	all req195, req196: Request, app1: NonTrusted, obj, obj1, obj2:OS_Object  |
		P_195[req195, app1, obj1, obj2] and 
		P_196[req196, obj] and 
		req195.per[Request] != req196.per[Request]
}

assert C_195_208{
	all req195, req208: Request, app1: NonTrusted, obj1, obj2:OS_Object |
		P_195[req195, app1, obj1, obj2] and 
		P_208[req208, app1, obj1, obj2] and 
		req195.per[Request] != req208.per[Request]
}

assert C_195_355{
	all req195, req355: Request, app1: NonTrusted, obj1, obj2:OS_Object |
		P_195[req195, app1, obj1, obj2] and 
		P_355[req355, app1, obj1] and 
		req195.per[Request] != req355.per[Request]
}

assert C_195_087{
	all req087, req195: Request, app1: NonTrusted, obj, obj1, obj2:OS_Object  |
		P_087[req087, obj] and 
		P_195[req195, app1, obj1, obj2] and 
		req087.per[Request] != req195.per[Request]
}

assert C_195_SameApp{
	all req195, reqSA: Request, app1: NonTrusted, app2: OS_App, obj1, obj2:OS_Object |
		P_195[req195, app1, obj1, obj2] and 
		P_SameApp[reqSA, app2, obj2] and 
		req195.per[Request] != reqSA.per[Request]
}

assert C_195_DiffApp{
	all req195, reqDA: Request, app1: NonTrusted, app2: OS_App, obj1, obj2:OS_Object |
		P_195[req195, app1, obj1, obj2] and 
		P_DiffApp[reqDA, app1, app2, obj1] and 
		req195.per[Request] != reqDA.per[Request]
}

assert C_195_GenStack{
	all req195, reqGS: Request, app1: NonTrusted, app2: OS_App, obj1, obj2:OS_Object |
		P_195[req195, app1, obj1, obj2] and 
		P_GenStack[reqGS, app2, obj1] and 
		req195.per[Request] != reqGS.per[Request]
}

//356
assert C_356_086{
	all req356, req086: Request, app: OS_App, app1: NonTrusted|
		P_356[req356, app1, app] and 
		P_086[req086,app] and 
		req356.per[Request] != req086.per[Request]
}

assert C_356_026{
	all req356, req026: Request, app1: NonTrusted, app2: OS_App|
		P_356[req356, app1, app2] and 
		P_026[req026, app1, app2] and 
		req356.per[Request] != req026.per[Request]
}

assert C_356_207{
	all req356, req207: Request, app1: NonTrusted, app2: OS_App |
		P_356[req356, app1, app2] and 
		P_207[req207, app1, app2] and 
		req356.per[Request] != req207.per[Request]
}

assert C_356_196{
	all req356, req196: Request, app1: NonTrusted, app2: OS_App, obj :OS_Object |
		P_356[req356, app1, app2] and 
		P_196[req196, obj] and 
		req356.per[Request] != req196.per[Request]
}

assert C_356_208{
	all req356, req208: Request, app1: NonTrusted, app2: OS_App, obj1, obj2:OS_Object|
		P_356[req356, app1, app2] and 
		P_208[req208, app1, obj1, obj2] and 
		req356.per[Request] != req208.per[Request]
}

assert C_356_355{
	all req356, req355: Request, app1: NonTrusted, app2:OS_App, obj1:OS_Object  |
		P_356[req356, app1, app2] and 
		P_355[req355, app1, obj1] and 
		req356.per[Request] != req355.per[Request]
}

assert C_356_087{
	all req087, req356: Request, app1: NonTrusted, app2: OS_App, obj:OS_Object  |
		P_087[req087, obj] and 
		P_356[req356, app1, app2] and 
		req087.per[Request] != req356.per[Request]
}

assert C_356_195{
	all req195, req356: Request, app1: NonTrusted, app2: OS_App, obj1, obj2:OS_Object |
		P_195[req195, app1, obj1, obj2] and 
		P_356[req356, app1, app2] and 
		req195.per[Request] != req356.per[Request]
}

assert C_356_SameApp{
	all req356, reqSA: Request, app1: NonTrusted, app2:OS_App, obj1:OS_Object  |
		P_356[req356, app1, app2] and 
		P_SameApp[reqSA, app2, obj1] and 
		req356.per[Request] != reqSA.per[Request]
}

assert C_356_DiffApp{
	all req356, reqDA: Request, app1: NonTrusted, app2:OS_App, obj1:OS_Object  |
		P_356[req356, app1, app2] and 
		P_DiffApp[reqDA, app1, app2, obj1] and 
		req356.per[Request] != reqDA.per[Request]
}

assert C_356_GenStack{
	all req356, reqGS: Request, app1: NonTrusted, app2:OS_App, obj1:OS_Object  |
		P_356[req356, app1, app2] and 
		P_GenStack[reqGS, app2, obj1] and 
		req356.per[Request] != reqGS.per[Request]
}

//Gen Data
assert C_GenData_026{
	all reqGD, req026: Request, app1: NonTrusted, app2: OS_App, obj: OS_Object|
		P_GenData[reqGD, app2, obj] and 
		P_026[req026, app1, app2] and 
		reqGD.per[Request] != req026.per[Request]
}

assert C_GenData_086{
	all reqGD, req086: Request, app2: OS_App, obj: OS_Object|
		P_GenData[reqGD, app2, obj] and 
		P_086[req086, app2] and 
		reqGD.per[Request] != req086.per[Request]
}

assert C_GenData_207{
	all reqGD, req207: Request, app1: NonTrusted, app2: OS_App, obj: OS_Object|
		P_GenData[reqGD, app2, obj] and 
		P_207[req207, app1, app2] and 
		reqGD.per[Request] != req207.per[Request]
}

assert C_GenData_196{
	all reqGD, req196: Request, app2: OS_App, obj: OS_Object|
		P_GenData[reqGD, app2, obj] and 
		P_196[req196, obj] and 
		reqGD.per[Request] != req196.per[Request]
}

assert C_GenData_208{
	all reqGD, req208: Request, app1: NonTrusted, app2: OS_App, obj1, obj2:OS_Object |
		P_GenData[reqGD, app2, obj1] and 
		P_208[req208, app1, obj1, obj2] and 
		reqGD.per[Request] != req208.per[Request]
}

assert C_GenData_355{
	all reqGD, req355: Request, app1: NonTrusted, app2: OS_App, obj1, obj2:OS_Object |
		P_GenData[reqGD, app2, obj2] and 
		P_355[req355, app1, obj1] and 
		reqGD.per[Request] != req355.per[Request]
}

assert C_GenData_356{
	all reqGD, req356: Request, app1: NonTrusted, app2: OS_App, obj2:OS_Object |
		P_GenData[reqGD, app2, obj2] and 
		P_356[req356, app1, app2] and 
		reqGD.per[Request] != req356.per[Request]
}

assert C_GenData_087{
	all reqGD, req087: Request, app2: OS_App, obj: OS_Object|
		P_GenData[reqGD, app2, obj] and 
		P_087[req087, obj] and 
		reqGD.per[Request] != req087.per[Request]
}

assert C_GenData_195{
	all req195, reqGD: Request, app1: NonTrusted, app2: OS_App, obj1, obj2:OS_Object |
		P_195[req195, app1, obj1, obj2] and 
		P_GenData[reqGD, app2, obj1] and 
		req195.per[Request] != reqGD.per[Request]
}

assert C_GenData_SameApp{
	all reqGD, reqSA: Request, app2: OS_App, obj: OS_Object|
		P_GenData[reqGD, app2, obj] and 
		P_SameApp[reqSA, app2, obj] and 
		reqGD.per[Request] != reqSA.per[Request]
}

assert C_GenData_DiffApp{
	all reqGD, reqDA: Request, app1: NonTrusted, app2: OS_App, obj: OS_Object|
		P_GenData[reqGD, app2, obj] and 
		P_DiffApp[reqDA, app1, app2, obj] and 
		reqGD.per[Request] != reqDA.per[Request]
}

assert C_GenData_GenStack{
	all reqGD, reqGS: Request, app2: OS_App, obj: OS_Object|
		P_GenData[reqGD, app2, obj] and 
		P_GenStack[reqGS, app2, obj] and 
		reqGD.per[Request] != reqGS.per[Request]
}

//Gen Stack 2

assert C_GenStack2_086{
	all reqGS2, req086: Request, app: OS_App, obj1, obj2:OS_Object|
		P_GenStack2[reqGS2, app, obj1, obj2] and
		P_086[req086,app] and 
		reqGS2.per[Request] != req086.per[Request]
}

assert C_GenStack2_026{
	all reqGS2, req026: Request, app1: NonTrusted, app2: OS_App, obj1, obj2:OS_Object|
		P_GenStack2[reqGS2, app2, obj1, obj2] and 
		P_026[req026, app1, app2] and 
		reqGS2.per[Request] != req026.per[Request]
}

assert C_GenStack2_207{
	all reqGS2, req207: Request, app1: NonTrusted, app2: OS_App, obj1, obj2:OS_Object |
		P_GenStack2[reqGS2, app2, obj1, obj2] and 
		P_207[req207, app1, app2] and 
		reqGS2.per[Request] != req207.per[Request]
}

assert C_GenStack2_196{
	all reqGS2, req196: Request, app1: OS_App, obj1, obj2:OS_Object|
		P_GenStack2[reqGS2, app1, obj1, obj2] and 
		P_196[req196, obj2] and 
		reqGS2.per[Request] != req196.per[Request]
}

assert C_GenStack2_SameApp{
	all reqGS2, reqSA: Request, app: OS_App, obj1, obj2:OS_Object|
		P_GenStack2[reqGS2, app, obj1, obj2] and
		P_SameApp[reqSA,app, obj1] and 
		reqGS2.per[Request] != reqSA.per[Request]
}

assert C_GenStack2_DiffApp{
	all reqGS2, reqDA: Request, app1: NonTrusted, app: OS_App, obj1, obj2:OS_Object|
		P_GenStack2[reqGS2, app1, obj1, obj2] and
		P_DiffApp[reqDA, app1, app, obj1] and 
		reqGS2.per[Request] != reqDA.per[Request]
}

assert C_GenStack2_208{
	all reqGS2, req208: Request, app1: NonTrusted, app2:OS_App, obj1, obj2:OS_Object|
		P_GenStack2[reqGS2, app2, obj1, obj2] and
		P_208[req208, app1, obj1, obj2] and 
		reqGS2.per[Request] != req208.per[Request]
}

assert C_GenStack2_087{
	all reqGS2, req087: Request, app: OS_App, obj1, obj2:OS_Object|
		P_GenStack2[reqGS2, app, obj1, obj2] and
		P_087[req087, obj1] and 
		reqGS2.per[Request] != req087.per[Request]
}

assert C_GenStack2_195{
	all reqGS2, req195: Request, app1: NonTrusted, app: OS_App, obj1, obj2:OS_Object|
		P_GenStack2[reqGS2, app, obj1, obj2] and
		P_195[req195, app1, obj1, obj2] and 
		reqGS2.per[Request] != req195.per[Request]
}

assert C_GenStack2_355{
	all reqGS2, req355: Request, app1: NonTrusted, app: OS_App, obj1, obj2:OS_Object|
		P_GenStack2[reqGS2, app, obj1, obj2] and
		P_355[req355, app1, obj1] and 
		reqGS2.per[Request] != req355.per[Request]
}

assert C_GenStack2_356{
	all reqGS2, req356: Request, app1: NonTrusted, app: OS_App, obj1, obj2:OS_Object|
		P_GenStack2[reqGS2, app, obj1, obj2] and
		P_356[req356, app1, app] and 
		reqGS2.per[Request] != req356.per[Request]
}

assert C_GenStack2_GenData{
	all reqGS2, reqDA: Request, app: OS_App, obj1, obj2:OS_Object|
		P_GenStack2[reqGS2, app, obj1, obj2] and
		P_GenData[reqDA, app, obj1] and 
		reqGS2.per[Request] != reqDA.per[Request]
}

assert C_GenStack2_GenStack{
	all reqGS2, reqGS: Request,app: OS_App, obj1, obj2:OS_Object|
		P_GenStack2[reqGS2, app, obj1, obj2] and
		P_GenStack[reqGS, app, obj1] and 
		reqGS2.per[Request] != reqGS.per[Request]
}

//-----------------------------------------------------------------------------------------------------------------------------------
run P_All{
	all req: Request, app1: NonTrusted, app, app2: OS_App, 
			obj, obj1, obj2:OS_Object |
		(P_026[req, app1, app2] implies req.per[Request] = May_Prevent) and
		(P_086[req, app] implies req.per[Request] = Shall_Permit) and
		(P_207[req, app1, app2] implies req.per[Request] = Shall_Prevent) and
		(P_196[req, obj] implies req.per[Request] = Shall_Permit) and
		(P_208[req, app, obj1, obj2] implies req.per[Request] = May_Prevent) and
		(P_355[req, app, obj] implies req.per[Request] = Shall_Prevent) and
		(P_087[req, obj] implies req.per[Request] = Shall_Permit) and
		(P_195[req, app, obj1, obj2] implies req.per[Request] = May_Prevent) and
		(P_356[req, app1, app2] implies req.per[Request] = Shall_Prevent) 
} for 8 but 2 OS_App
run P_GenStack2_GenStack{
	all reqGS2: Request,app: OS_App, obj1, obj2:OS_Object|
		(P_GenStack2[reqGS2, app, obj1, obj2] implies reqGS2.per[Request]=Shall_Prevent) and
		(P_GenStack[reqGS2, app, obj1] implies reqGS2.per[Request]=May_Permit)
	//	P_GenStack[reqGS, app, obj1]  
		
}



check C_GenStack2_GenStack
check C_GenStack2_GenData
check C_GenStack2_207
check C_GenStack2_087
check C_GenStack2_356
check C_GenStack2_DiffApp
check C_GenStack2_SameApp
check C_GenStack2_355
check C_GenStack2_208
check C_GenStack2_196
check C_GenStack2_207
check C_GenStack2_026
check C_GenStack2_086

check C_GenData_GenStack 
check C_GenData_DiffApp
check C_GenData_SameApp
check C_GenData_356
check C_GenData_355
check C_GenData_195
check C_GenData_087
check C_GenData_208
check C_GenData_207
check C_GenData_196
check C_GenData_086
check C_GenData_026
check C_356_GenStack
check C_356_DiffApp
check C_356_SameApp
check C_356_195
check C_356_355
check C_356_208
check C_356_207
check C_356_087
check C_356_196
check C_356_026
check C_356_086
check C_195_GenStack
check C_195_DiffApp
check C_195_SameApp
check C_195_355
check C_195_208
check C_195_207
check C_195_087
check C_195_196
check C_195_026
check C_195_086
check C_087_GenStack
check C_087_DiffApp
check C_087_SameApp
check C_087_355
check C_087_208
check C_087_207
check C_087_026
check C_087_196
check C_087_086
check C_GenStack_DiffApp
check C_GenStack_SameApp
check C_GenStack_355
check C_GenStack_208
check C_GenStack_196
check C_GenStack_207
check C_GenStack_026
check C_GenStack_086
check C_355_DiffApp
check C_355_SameApp
check C_355_208
check C_355_196
check C_355_207
check C_355_026
check C_355_086
check C_208_DiffApp
check C_208_SameApp
check C_208_196
check C_208_207
check C_208_026
check C_208_086
check C_196_SameApp
check C_196_DiffApp
check C_196_207
check C_196_026
check C_196_086
check C_DiffApp_SameApp
check C_DiffApp_207
check C_DiffApp_086
check C_DiffApp_026
check C_SameApp_207
check C_SameApp_086
check C_SameApp_026
check C_207_026
check C_207_086
check C_026_086

