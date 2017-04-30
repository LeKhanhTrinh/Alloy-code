module mem_pro_9

//An object in the operating system
abstract sig OS_Object {
	parent: lone OS_App,
	Data_Sect: lone DataSections,
	Stack: lone Stacks
}

//An application in the operating system
sig OS_App extends OS_Object{
	contains: some OS_Object
} {	
	no parent
	lone Data_Sect
	no Stack
	}

sig Trusted, NonTrusted extends OS_App {} 

//A Task or ISR
sig Task, ISR extends OS_Object{} {
	one Data_Sect
	one Stack
}
sig Cate_1, Cate_2 extends ISR{}

//Memory of an applications or object
abstract sig Memory{}

sig DataSections, Stacks extends Memory{
	belongTo: one OS_Object
}

//System status
abstract sig Status{}
one sig May_Prevent, May_Permit, 
	Shall_Prevent,  Shall_Permit extends Status{}

abstract sig Action{}
one sig Read, Write extends Action{}

//The Request Access to Memory
sig Request{
	from: OS_Object,
	to: Memory,
	act: Action,
	per: Status
}

/*An OS_App is the parent of what is contained
All Objects are OS_App, Tasks, and ISR
*/
fact{
	//An OS_Object is the parent of what is contained
	all app: OS_App, cont: app.contains |
		cont.parent = app
	all obj: OS_Object,  ds: obj.Data_Sect |
		ds.belongTo = obj
	all obj: OS_Object,  stk: obj.Stack |
		stk.belongTo = obj
	
	/**
		OS-Application’s  private  data  sections  are  shared  by  all 
		Tasks/ISRs belonging to that OS-Application
	*/
	all req: Request, app: OS_App, obj: OS_Object |
		obj.parent = app and 
		req.from = obj and 
		req.to = app.Data_Sect and
		(req.act = Read or req.act = Write) and
		req.per = Shall_Permit

	/**
		The  stack  belongs only to the owner object and 
		no  need  to  share  stack  data  between  objects
	*/
	all req: Request, obj1, obj2: OS_Object |
		req.from = obj1 and 
		req.to = obj2.Stack and
		(req.act = Read or req.act = Write) and
		obj1 != obj2 and
		req.per = Shall_Prevent


	//OS_Object including Tasks, ISRs, and OS_Apps
	Task + ISR + OS_App = OS_Object
}

//Create the initialization for model
one sig Start{
	empty: one OS_App
}

fact Initialization{
	OS_App in (Start.empty).*{x: OS_App, y: x.contains}
}
// ------------------------------------------------------------------------------------------------------------------------
// 026_086_207_355_356
fact constraint_set{
	//026: From App1 to App2's DS
	all req: Request, app1: NonTrusted, app2: OS_App | 
		P_026[req, app1, app2] implies req.per = May_Prevent

	//086: From App to App's Data
	all req: Request, app: OS_App| 
		P_086[req, app] implies req.per = Shall_Permit

	//207: From App1 to App2's DS
	all req: Request, app1: NonTrusted, app2: OS_App | 
		P_207[req, app1, app2] implies req.per = Shall_Prevent

	//----------------------------------------------------------------------------------------------------------------
	//196: From Obj to Obj's Stack
	all req: Request, obj: OS_Object| 
		P_196[req, obj] implies req.per = Shall_Permit

	//208: from Obj1 to Obj2's Stack
	all req: Request, app: NonTrusted, obj1, obj2: OS_Object | 
		P_208[req, app, obj1, obj2] implies req.per = May_Prevent

	//355: from App to App2.obj.Stack
	all req: Request, app: NonTrusted, obj: OS_Object| 
		P_355[req, app, obj] implies req.per = Shall_Prevent
	
	//----------------------------------------------------------------------------------------------------------------
	//087: From Obj to Obj.Ds
	all req: Request, obj: OS_Object | 
		P_087[req, obj] implies req.per = Shall_Permit

	//195: From app.obj1 to app.obj2.DS
	all req: Request, app: NonTrusted, obj1, obj2: OS_Object| 
		P_195[req, app, obj1, obj2] implies req.per = May_Prevent

	//356: From app1 to app2.DS
	all req: Request, app1: NonTrusted, app2: OS_App| 
		P_356[req, app1, app2] implies req.per = Shall_Prevent

}

//Private data of an OS-APP
//-----------------------------------------------------------------------------------------------------------------------------------
// 086
//R&W: From App to App's Data
pred P_086 [req: Request, app: OS_App]{
	(req.act = Read or req.act = Write) 
	req.from = app  
	req.to = app.Data_Sect 
}
// 207
//W: From App1 to App2's DS
pred P_207 [req: Request, app1: NonTrusted, app2: OS_App]{
	app1 != app2
	req.from = app1
	req.to = app2.Data_Sect
	req.act = Write
}
// 026
//R: From App1 to App2's DS
pred P_026 [req: Request, app1: NonTrusted, app2: OS_App]{
	app1 != app2
	req.from = app1
	req.to = app2.Data_Sect
	req.act = Read
}

//gen1
//R&W: From obj to the App.data
pred P_SameApp[req: Request, app: OS_App, obj: OS_Object]{
	obj.parent = app
	req.from = obj
	req.to = app.Data_Sect
	(req.act = Read or req.act = Write)
}

//gen2
pred P_DiffApp[req: Request, app1, app2: OS_App, obj: OS_Object]{
	app1 != app2
	obj.parent = app1
	req.from = obj
	req.to = app2.Data_Sect
	(req.act = Read or req.act = Write)
}

//Private stack of an Os Object
//-----------------------------------------------------------------------------------------------------------------------------------
//gen3
//R&W: From app to obj.stack
pred P_GenStack[req: Request, app: OS_App, obj: OS_Object]{
	req.from = app
	obj.parent = app
	req.to = obj.Stack
	(req.act = Read or req.act  = Write)
}

//196
//R&W: From Obj to Obj's Stack
pred P_196 [req: Request, obj: OS_Object]{
	(req.act = Read or req.act = Write) 
	req.from = obj  
	req.to = obj.Stack 
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
	req.to = obj2.Stack  
}
// 355
//W: from App to App2.obj.Stack
pred P_355 [req: Request, app: NonTrusted, obj: OS_Object]{
	obj.parent = OS_App
	app != obj.parent
	req.act = Write
	req.from = app
	req.to = obj.Stack
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
	req.to = obj2.Stack  
}

//Private data of an Os Object
//-----------------------------------------------------------------------------------------------------------------------------------
//gen4
//R&W: From app to obj.data
pred P_GenData[req: Request, app: OS_App, obj: OS_Object]{
	req.from = app
	obj.parent = app
	req.to = obj.Data_Sect
	(req.act = Read or req.act  = Write)
}

// 087
//R&W: From Obj to Obj.Ds
pred P_087 [req: Request, obj: OS_Object]{
	(req.act = Read or req.act = Write) 
	req.from = obj  
	req.to = obj.Data_Sect 
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
	req.to = obj2.Data_Sect  
}
// 356
//W: From app1 to app2.DS
pred P_356 [req: Request, app1: NonTrusted, app2: OS_App]{
	app1 != app2
	req.from = app1
	req.to = app2.Data_Sect
	req.act = Write
}

////-----------------------------------------------------------------------------------------------------------------------------------
//Assertions
assert C_026_086{
	some req: Request, app1: NonTrusted, app2: OS_App|
		P_026[req, app1, app2] and 
		P_086[req, app2] 
}

//207
assert C_207_086{
	some req: Request, app1: NonTrusted, app2: OS_App |
		P_207[req, app1, app2] and 
		P_086[req,app2]
}

assert C_207_026{
	some req: Request, app1: NonTrusted, app2: OS_App|
		P_207[req, app1, app2] and 
		P_026[req, app1, app2] 
}

//Same App
assert C_SameApp_026{
	some req: Request, app1: NonTrusted, app2: OS_App, obj: OS_Object|
		P_SameApp[req, app2, obj] and
		P_026[req, app1, app2]
}

assert C_SameApp_086{
	some req: Request, app: OS_App, obj: OS_Object|
		P_SameApp[req, app, obj] and
		P_086[req, app]
}

assert C_SameApp_207{
	some req: Request, app1: NonTrusted, app2: OS_App, obj: OS_Object|
		P_SameApp[req, app2, obj] and
		P_207[req, app1, app2] 
}

// Different App
assert C_DiffApp_026{
	some req: Request, app1: NonTrusted, app2: OS_App, obj: OS_Object|
		P_DiffApp[req, app1, app2, obj] and
		P_026[req, app1, app2]
}

assert C_DiffApp_086{
	some req: Request, app1: NonTrusted, app2: OS_App, obj: OS_Object|
		P_DiffApp[req, app1, app2, obj] and
		P_086[req, app2]
}

assert C_DiffApp_207{
	some req: Request, app1: NonTrusted, app2: OS_App, obj: OS_Object|
		P_DiffApp[req, app1, app2, obj] and
		P_207[req, app1, app2] 
}

assert C_DiffApp_SameApp{
	some req: Request, app1: NonTrusted, app2: OS_App, obj: OS_Object|
		P_DiffApp[req, app1, app2, obj] and
		P_SameApp[req, app2, obj]
}

//196
assert C_196_086{
	some req: Request, obj: OS_Object, app: OS_App|
		P_196[req, obj] and 
		P_086[req,app] 
}

assert C_196_026{
	some req: Request, app1: NonTrusted, app2: OS_App, obj:OS_Object|
		P_196[req, obj] and 
		P_026[req, app1, app2]
}

assert C_196_207{
	some req: Request, app1: NonTrusted, app2: OS_App, obj:OS_Object |
		P_196[req, obj] and 
		P_207[req, app1, app2] 
}

assert C_196_DiffApp{
	some req: Request, app1: NonTrusted, app2: OS_App, obj:OS_Object |
		P_196[req, obj] and 
		P_DiffApp[req, app1, app2, obj] 
}

assert C_196_SameApp{
	some req: Request, obj: OS_Object, app: OS_App|
		P_196[req, obj] and 
		P_SameApp[req,app, obj] 
}

//208
assert C_208_086{
	some req: Request, app1: NonTrusted, app: OS_App, obj1, obj2:OS_Object|
		P_208[req, app1, obj1, obj2] and
		P_086[req,app] 
}

assert C_208_026{
	some req: Request, app1: NonTrusted, app2: OS_App, obj1, obj2:OS_Object|
		P_208[req, app1, obj1, obj2] and 
		P_026[req, app1, app2] 
}

assert C_208_207{
	some req: Request, app1: NonTrusted, app2: OS_App, obj1, obj2:OS_Object |
		P_208[req, app1, obj1, obj2] and 
		P_207[req, app1, app2]
}

assert C_208_196{
	some req: Request, app1: NonTrusted, obj1, obj2:OS_Object|
		P_208[req, app1, obj1, obj2] and 
		P_196[req, obj2] 
}

assert C_208_SameApp{
	some req: Request, app1: NonTrusted, app: OS_App, obj1, obj2:OS_Object|
		P_208[req, app1, obj1, obj2] and
		P_SameApp[req,app, obj1] 
}

assert C_208_DiffApp{
	some req: Request, app1: NonTrusted, app: OS_App, obj1, obj2:OS_Object|
		P_208[req, app1, obj1, obj2] and
		P_DiffApp[req, app1, app, obj1]
}

//355
assert C_355_086{
	some req: Request, app1: NonTrusted, app: OS_App, obj:OS_Object |
		P_355[req, app1, obj] and 
		P_086[req,app] 
}

assert C_355_026{
	some req: Request, app1: NonTrusted, app2: OS_App, obj:OS_Object|
		P_355[req, app1, obj] and 
		P_026[req, app1, app2]
}

assert C_355_207{
	some req: Request, app1: NonTrusted, app2: OS_App, obj:OS_Object |
		P_355[req, app1, obj] and 
		P_207[req, app1, app2] 
}

assert C_355_196{
	some req: Request, app1: NonTrusted, obj1, obj2:OS_Object  |
		P_355[req, app1, obj1] and 
		P_196[req, obj2]
}

assert C_355_208{
	some req: Request, app1: NonTrusted, obj, obj1, obj2:OS_Object |
		P_355[req, app1, obj] and 
		P_208[req, app1, obj1, obj2] 
}

assert C_355_SameApp{
	some req: Request, app1: NonTrusted, app: OS_App, obj, obj1:OS_Object |
		P_355[req, app1, obj] and 
		P_SameApp[req,app, obj1]
}

assert C_355_DiffApp{
	some req: Request, app1: NonTrusted, app: OS_App, obj, obj1:OS_Object |
		P_355[req, app1, obj] and 
		P_DiffApp[req,app1, app, obj1]
}

//GenStack
assert C_GenStack_086{
	some req: Request, app2: OS_App, obj2:OS_Object |
		P_GenStack[req, app2, obj2] and 
		P_086[req,app2] 
}

assert C_GenStack_026{
	some req: Request, app1: NonTrusted, app2: OS_App, obj2:OS_Object |
		P_GenStack[req, app2, obj2] and 
		P_026[req, app1, app2]
}

assert C_GenStack_207{
	some req: Request, app1: NonTrusted, app2: OS_App, obj:OS_Object |
		P_GenStack[req, app2, obj] and 
		P_207[req, app1, app2]
}

assert C_GenStack_196{
	some req: Request, app2: OS_App, obj1, obj2:OS_Object  |
		P_GenStack[req, app2, obj1] and 
		P_196[req, obj2] 
}

assert C_GenStack_208{
	some req: Request, app1: NonTrusted, app2: OS_App, obj, obj1, obj2:OS_Object |
		P_GenStack[req, app2, obj] and 
		P_208[req, app1, obj1, obj2] 
}

assert C_GenStack_SameApp{
	some req: Request, app: OS_App, obj, obj1:OS_Object |
		P_GenStack[req, app, obj] and 
		P_SameApp[req, app, obj1]
}

assert C_GenStack_DiffApp{
	some req: Request, app1: NonTrusted, app2: OS_App, obj, obj1:OS_Object |
		P_GenStack[req, app2, obj] and 
		P_DiffApp[req,app1, app2, obj1] 
}

assert C_GenStack_355{
	some req: Request, app1: NonTrusted, app2: OS_App, obj, obj1:OS_Object |
		P_GenStack[req, app2, obj] and 
		P_355[req,app1, obj1] 
}

//087
assert C_087_086{
	some req: Request, app: OS_App, obj:OS_Object |
		P_087[req, obj] and 
		P_086[req,app] 
}

assert C_087_026{
	some req: Request, app1: NonTrusted, app2: OS_App, obj:OS_Object|
		P_087[req, obj] and 
		P_026[req, app1, app2]
}

assert C_087_207{
	some req: Request, app1: NonTrusted, app2: OS_App, obj:OS_Object|
		P_087[req, obj] and 
		P_207[req, app1, app2]
}

assert C_087_196{
	some req: Request, obj:OS_Object  |
		P_087[req, obj] and 
		P_196[req, obj] 
}

assert C_087_208{
	some req: Request, app1: NonTrusted, obj, obj1, obj2:OS_Object |
		P_087[req, obj] and 
		P_208[req, app1, obj1, obj2] 
}

assert C_087_355{
	some req: Request, app1: NonTrusted, obj, obj1:OS_Object |
		P_087[req, obj] and 
		P_355[req, app1, obj1] 
}

assert C_087_SameApp{
	some  req: Request, app2: OS_App, obj, obj1:OS_Object |
		P_087[req, obj] and 
		P_SameApp[req, app2, obj1] 
}

assert C_087_DiffApp{
	some  req: Request, app1: NonTrusted, app2: OS_App, obj, obj1:OS_Object |
		P_087[req, obj] and 
		P_DiffApp[req, app1, app2, obj1] 
}

assert C_087_GenStack{
	some  req: Request, app2: OS_App, obj, obj1:OS_Object |
		P_087[req, obj] and 
		P_GenStack[req, app2, obj1] 
}

//195
assert C_195_086{
	some  req: Request, app: OS_App, app1: NonTrusted, obj1, obj2:OS_Object |
		P_195[req, app1, obj1, obj2] and 
		P_086[req,app] 
}

assert C_195_026{
	some  req: Request, app1: NonTrusted, app2: OS_App, obj1, obj2:OS_Object |
		P_195[req, app1, obj1, obj2] and 
		P_026[req, app1, app2] 
}

assert C_195_207{
	some  req: Request, app1: NonTrusted, app2: OS_App, obj1, obj2:OS_Object |
		P_195[req, app1, obj1, obj2] and 
		P_207[req, app1, app2]
}

assert C_195_196{
	some  req: Request, app1: NonTrusted, obj, obj1, obj2:OS_Object  |
		P_195[req, app1, obj1, obj2] and 
		P_196[req, obj] 
}

assert C_195_208{
	some  req: Request, app1: NonTrusted, obj1, obj2:OS_Object |
		P_195[req, app1, obj1, obj2] and 
		P_208[req, app1, obj1, obj2] 
}

assert C_195_355{
	some  req: Request, app1: NonTrusted, obj1, obj2:OS_Object |
		P_195[req, app1, obj1, obj2] and 
		P_355[req, app1, obj1]
}

assert C_195_087{
	some  req: Request, app1: NonTrusted, obj, obj1, obj2:OS_Object  |
		P_087[req, obj] and 
		P_195[req, app1, obj1, obj2] 
}

assert C_195_SameApp{
	some  req: Request, app1: NonTrusted, app2: OS_App, obj1, obj2:OS_Object |
		P_195[req, app1, obj1, obj2] and 
		P_SameApp[req, app2, obj2] 
}

assert C_195_DiffApp{
	some  req: Request, app1: NonTrusted, app2: OS_App, obj1, obj2:OS_Object |
		P_195[req, app1, obj1, obj2] and 
		P_DiffApp[req, app1, app2, obj1]
}

assert C_195_GenStack{
	some  req: Request, app1: NonTrusted, app2: OS_App, obj1, obj2:OS_Object |
		P_195[req, app1, obj1, obj2] and 
		P_GenStack[req, app2, obj1] 
}

//356
assert C_356_086{
	some  req: Request, app: OS_App, app1: NonTrusted|
		P_356[req, app1, app] and 
		P_086[req,app] 
}

assert C_356_026{
	some  req: Request, app1: NonTrusted, app2: OS_App|
		P_356[req, app1, app2] and 
		P_026[req, app1, app2] 
}

assert C_356_207{
	some  req: Request, app1: NonTrusted, app2: OS_App |
		P_356[req, app1, app2] and 
		P_207[req, app1, app2]
}

assert C_356_196{
	some  req: Request, app1: NonTrusted, app2: OS_App, obj :OS_Object |
		P_356[req, app1, app2] and 
		P_196[req, obj] 
}

assert C_356_208{
	some  req: Request, app1: NonTrusted, app2: OS_App, obj1, obj2:OS_Object|
		P_356[req, app1, app2] and 
		P_208[req, app1, obj1, obj2] 
}

assert C_356_355{
	some  req: Request, app1: NonTrusted, app2:OS_App, obj1:OS_Object  |
		P_356[req, app1, app2] and 
		P_355[req, app1, obj1]
}

assert C_356_087{
	some  req: Request, app1: NonTrusted, app2: OS_App, obj:OS_Object  |
		P_087[req, obj] and 
		P_356[req, app1, app2] 
}

assert C_356_195{
	some  req: Request, app1: NonTrusted, app2: OS_App, obj1, obj2:OS_Object |
		P_195[req, app1, obj1, obj2] and 
		P_356[req, app1, app2] 
}

assert C_356_SameApp{
	some  req: Request, app1: NonTrusted, app2:OS_App, obj1:OS_Object  |
		P_356[req, app1, app2] and 
		P_SameApp[req, app2, obj1] 
}

assert C_356_DiffApp{
	some  req: Request, app1: NonTrusted, app2:OS_App, obj1:OS_Object  |
		P_356[req, app1, app2] and 
		P_DiffApp[req, app1, app2, obj1] 
}

assert C_356_GenStack{
	some  req: Request, app1: NonTrusted, app2:OS_App, obj1:OS_Object  |
		P_356[req, app1, app2] and 
		P_GenStack[req, app2, obj1]
}

//Gen Data
assert C_GenData_026{
	some  req: Request, app1: NonTrusted, app2: OS_App, obj: OS_Object|
		P_GenData[req, app2, obj] and 
		P_026[req, app1, app2] 
}

assert C_GenData_086{
	some  req: Request, app2: OS_App, obj: OS_Object|
		P_GenData[req, app2, obj] and 
		P_086[req, app2]
}

assert C_GenData_207{
	some  req: Request, app1: NonTrusted, app2: OS_App, obj: OS_Object|
		P_GenData[req, app2, obj] and 
		P_207[req, app1, app2] 
}

assert C_GenData_196{
	some  req: Request, app2: OS_App, obj: OS_Object|
		P_GenData[req, app2, obj] and 
		P_196[req, obj] 
}

assert C_GenData_208{
	some  req: Request, app1: NonTrusted, app2: OS_App, obj1, obj2:OS_Object |
		P_GenData[req, app2, obj1] and 
		P_208[req, app1, obj1, obj2] 
}

assert C_GenData_355{
	some  req: Request, app1: NonTrusted, app2: OS_App, obj1, obj2:OS_Object |
		P_GenData[req, app2, obj2] and 
		P_355[req, app1, obj1]
}

assert C_GenData_356{
	some  req: Request, app1: NonTrusted, app2: OS_App, obj2:OS_Object |
		P_GenData[req, app2, obj2] and 
		P_356[req, app1, app2]
}

assert C_GenData_087{
	some  req: Request, app2: OS_App, obj: OS_Object|
		P_GenData[req, app2, obj] and 
		P_087[req, obj] 
}

assert C_GenData_195{
	some  req: Request, app1: NonTrusted, app2: OS_App, obj1, obj2:OS_Object |
		P_195[req, app1, obj1, obj2] and 
		P_GenData[req, app2, obj1] 
}

assert C_GenData_SameApp{
	some  req: Request, app2: OS_App, obj: OS_Object|
		P_GenData[req, app2, obj] and 
		P_SameApp[req, app2, obj] 
}

assert C_GenData_DiffApp{
	some  req: Request, app1: NonTrusted, app2: OS_App, obj: OS_Object|
		P_GenData[req, app2, obj] and 
		P_DiffApp[req, app1, app2, obj] 
}

assert C_GenData_GenStack{
	some  req: Request, app2: OS_App, obj: OS_Object|
		P_GenData[req, app2, obj] and 
		P_GenStack[req, app2, obj]
}

//Gen Stack 2

assert C_GenStack2_086{
	some  req: Request, app: OS_App, obj1, obj2:OS_Object|
		P_GenStack2[req, app, obj1, obj2] and
		P_086[req,app] 
}

assert C_GenStack2_026{
	some  req: Request, app1: NonTrusted, app2: OS_App, obj1, obj2:OS_Object|
		P_GenStack2[req, app2, obj1, obj2] and 
		P_026[req, app1, app2] 
}

assert C_GenStack2_207{
	some  req: Request, app1: NonTrusted, app2: OS_App, obj1, obj2:OS_Object |
		P_GenStack2[req, app2, obj1, obj2] and 
		P_207[req, app1, app2] 
}

assert C_GenStack2_196{
	some  req: Request, app1: OS_App, obj1, obj2:OS_Object|
		P_GenStack2[req, app1, obj1, obj2] and 
		P_196[req, obj2]
}

assert C_GenStack2_SameApp{
	some  req: Request, app: OS_App, obj1, obj2:OS_Object|
		P_GenStack2[req, app, obj1, obj2] and
		P_SameApp[req,app, obj1] 
}

assert C_GenStack2_DiffApp{
	some  req: Request, app1: NonTrusted, app: OS_App, obj1, obj2:OS_Object|
		P_GenStack2[req, app1, obj1, obj2] and
		P_DiffApp[req, app1, app, obj1]
}

assert C_GenStack2_208{
	some  req: Request, app1: NonTrusted, app2:OS_App, obj1, obj2:OS_Object|
		P_GenStack2[req, app2, obj1, obj2] and
		P_208[req, app1, obj1, obj2] 
}

assert C_GenStack2_087{
	some  req: Request, app: OS_App, obj1, obj2:OS_Object|
		P_GenStack2[req, app, obj1, obj2] and
		P_087[req, obj1] 
}

assert C_GenStack2_195{
	some  req: Request, app1: NonTrusted, app: OS_App, obj1, obj2:OS_Object|
		P_GenStack2[req, app, obj1, obj2] and
		P_195[req, app1, obj1, obj2]
}

assert C_GenStack2_355{
	some req: Request, app1: NonTrusted, app: OS_App, obj1, obj2:OS_Object|
		P_GenStack2[req, app, obj1, obj2] and
		P_355[req, app1, obj1] 
}

assert C_GenStack2_356{
	some req: Request, app1: NonTrusted, app: OS_App, obj1, obj2:OS_Object|
		P_GenStack2[req, app, obj1, obj2] and
		P_356[req, app1, app] 
}

assert C_GenStack2_GenData{
	some req: Request, app: OS_App, obj1, obj2:OS_Object|
		P_GenStack2[req, app, obj1, obj2] and
		P_GenData[req, app, obj1] 
}

assert C_GenStack2_GenStack{
	some req: Request,app: OS_App, obj1, obj2:OS_Object|
		P_GenStack2[req, app, obj1, obj2] and
		P_GenStack[req, app, obj1] 
}

//-----------------------------------------------------------------------------------------------------------------------------------
/*
run P_All{
	all req,req,req,req,req,req,req,
		req,req: Request, app1: NonTrusted, app, app2: OS_App, 
			obj, obj1, obj2:OS_Object |
		(P_026[req, app1, app2] implies req.per = May_Prevent) and
		(P_086[req, app] implies req.per = Shall_Permit) and
		(P_207[req, app1, app2] implies req.per = Shall_Prevent) and
		(P_196[req, obj] implies req.per = Shall_Permit) and
		(P_208[req, app, obj1, obj2] implies req.per = May_Prevent) and
		(P_355[req, app, obj] implies req.per = Shall_Prevent) and
		(P_087[req, obj] implies req.per = Shall_Permit) and
		(P_195[req, app, obj1, obj2] implies req.per = May_Prevent) and
		(P_356[req, app1, app2] implies req.per = Shall_Prevent) 
} 
run P_GenStack2_GenStack{
	all req: Request,app: OS_App, obj1, obj2:OS_Object|
		(P_GenStack2[req, app, obj1, obj2] implies req.per=Shall_Prevent) and
		(P_GenStack[req, app, obj1] implies req.per=May_Permit)
	//	P_GenStack[req, app, obj1]  
		
}
*/



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

