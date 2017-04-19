module mem_pro_5

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

	//Some obj1 and obj2 belong to the same OS_App
	some obj1,obj2: OS_Object, app1: obj1.parent, app2:obj2.parent |
		app1 = app2
	Task + ISR + OS_App = OS_Object
}

//Memory of an applications or object
abstract sig Memory{}

sig DataSections, Stacks extends Memory{
	belongTo: one OS_Object
}


//System status
abstract sig status{}
one sig may_prevent, may_permit, shall_prevent, 
shall_permit extends status{}

abstract sig action{}
one sig read, write extends action{}

//Accesses
sig accessObj{
	from: OS_Object,
	to: Memory,
	per: status,
	act: action
}

sig accessApp{
	from: OS_App,
	to: Memory,
	per: status,
	act: action
}

//Constraints
//From OS_App to other Objects memory
fact constants_026_086_207_355_356{
	all app1: NonTrusted, app2: OS_App, asc: accessApp, ds:app2.ownDS|
	//026
	(
		asc.act = read and
		asc.from = app1 and 
		asc.to = ds and 
		app1 != app2 and
		asc.per = may_prevent
	)
	//086
	all app: OS_App, asc: accessApp|	
	(
		(asc.act = read or asc.act = write) and
		asc.from = app and 
		asc.to = app.ownDS and
		asc.per = shall_permit
	)
	
	//207
	all app1: NonTrusted, app2: OS_App, asc: accessApp, ds:app2.ownDS|
	(
		asc.act = write and
		asc.from = app1 and 
		asc.to = ds and 
		app1 != app2 and
		asc.per = may_prevent
	)

	//355
	all app1: NonTrusted, app2: OS_App, obj: OS_Object, asc: accessApp, st:obj.ownSt|
	(
		asc.act = write and
		asc.from = app1 and
		asc.to = st and
		obj.parent = app2 and
		asc.per = shall_prevent
	)
	
	//356
	all app1: NonTrusted, app2: OS_App, obj: OS_Object, asc: accessApp, st:obj.ownSt|
	(
		asc.act = write and
		asc.from = app1 and
		asc.to = st and
		obj.parent = app2 and
		asc.per = shall_prevent
	)
}

fact constants_196_208_087_195{
	//196
	all obj: OS_Object, asc: accessObj, st:obj.ownSt |
	(
		(obj in Task or obj in Cate_2) and
		(asc.act = read or asc.act = write) and
		asc.from = obj and 
		asc.to = st and
		asc.per = shall_permit
	)

	//208
	all obj1, obj2: OS_Object, app: NonTrusted, asc: accessObj, st:obj2.ownSt |
	(
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
	all obj: OS_Object, asc: accessObj, ds:obj.ownDS |
	(
		(obj in Task or obj in Cate_2) and
		(asc.act = read or asc.act = write) and
		asc.from = obj and
		asc.to = ds and
		asc.per = shall_permit
	)
	
	//195
	all obj1, obj2: OS_Object, app: NonTrusted, asc: accessObj, ds:obj2.ownDS |
	(
		(obj1 in Task or obj1 in Cate_2) and
		(obj2 in Task or obj2 in Cate_2) and
		obj1.parent = app and
		obj2.parent = app and
		(obj1 != obj2) and
		asc.act = write and
		asc.from = obj1 and
		asc.to = ds and
		asc.per = may_prevent
	)
}
//------------------------------------------------------------------------------------------
//Exist a area that conflict 195 and 208
assert check_195_208{
	some app: NonTrusted, obj1, obj2: OS_Object, asc: accessApp,  ds:obj2.ownDS, st:obj2.ownSt|
	
		(obj1 in Task or obj1 in Cate_2) and
		(obj2 in Task or obj2 in Cate_2) and
		obj1.parent = app and
		obj2.parent = app and
		(obj1 != obj2) and
		asc.act = write and
		asc.from = obj1 and
		asc.to = st and
		asc.per = may_prevent
	 and
	(obj1 in Task or obj1 in Cate_2) and
		(obj2 in Task or obj2 in Cate_2) and
		obj1.parent = app and
		obj2.parent = app and
		(obj1 != obj2) and
		asc.act = write and
		asc.from = obj1 and
		asc.to = ds and
		asc.per = may_prevent
}

//Exist a area that conflict 195 and 087
assert check_195_087{
	some app: NonTrusted, obj,obj1, obj2: OS_Object, asc: accessObj,  ds:obj2.ownDS|
	
		(obj1 in Task or obj1 in Cate_2) and
		(obj2 in Task or obj2 in Cate_2) and
		obj1.parent = app and
		obj2.parent = app and
		(obj1 != obj2) and
		asc.act = write and
		asc.from = obj1 and
		asc.to = ds and
		asc.per = may_prevent
	 and
	(obj in Task or obj in Cate_2) and
		(asc.act = read or asc.act = write) and
		asc.from = obj and 
		asc.to = ds and
		asc.per = shall_permit
}

//Exist a area that conflict 195 and 356
assert check_195_196{
	some  app: NonTrusted, obj, obj1, obj2: OS_Object, asc: accessObj,  st:obj2.ownSt, ds:obj2.ownDS|
	(obj in Task or obj in Cate_2) and
		(asc.act = read or asc.act = write) and
		asc.from = obj and 
		asc.to = st and
		asc.per = shall_permit and
	(obj1 in Task or obj1 in Cate_2) and
		(obj2 in Task or obj2 in Cate_2) and
		obj1.parent = app and
		obj2.parent = app and
		(obj1 != obj2) and
		asc.act = write and
		asc.from = obj1 and
		asc.to = ds and
		asc.per = may_prevent
}

//Exist a area that conflict 195 and 356
assert check_195_356{
	some app1: NonTrusted, obj, obj1, obj2: OS_Object, app2: OS_App, asc: accessApp, asc1: accessObj, st:obj.ownSt, ds:obj2.ownDS|
	asc.act = write and
	asc.from = app1 and
	asc.to = st and
	obj.parent = app2 and
	asc.per = shall_prevent and
		(obj1 in Task or obj1 in Cate_2) and
		(obj2 in Task or obj2 in Cate_2) and
		obj1.parent = app1 and
		obj2.parent = app1 and
		(obj1 != obj2) and
		asc1.act = write and
		asc1.from = obj1 and
		asc1.to = ds and
		asc1.per = may_prevent
}

//Exist a area that conflict 195 and 355
assert check_195_355{
	some app1: NonTrusted, obj, obj1, obj2: OS_Object, app2: OS_App, asc: accessApp, asc1: accessObj, ds:obj2.ownDS, st1:obj.ownSt|
	(obj1 in Task or obj1 in Cate_2) and
		(obj2 in Task or obj2 in Cate_2) and
		obj1.parent = app1 and
		obj2.parent = app1 and
		(obj1 != obj2) and
		asc1.act = write and
		asc1.from = obj1 and
		asc1.to = ds and
		asc1.per = may_prevent and
	asc.act = write and
	asc.from = app1 and
	asc.to = st1 and
	obj.parent = app2 and
	asc.per = shall_prevent
}

//Exist a area that conflict 195 and 207
assert check_195_207{
	some app1: NonTrusted, obj, obj1, obj2: OS_Object, app2: OS_App, asc: accessApp, asc1: accessObj, ds:app2.ownDS, ds1:obj2.ownDS|
	(obj1 in Task or obj1 in Cate_2) and
		(obj2 in Task or obj2 in Cate_2) and
		obj1.parent = app1 and
		obj2.parent = app1 and
		(obj1 != obj2) and
		asc1.act = write and
		asc1.from = obj1 and
		asc1.to = ds1 and
		asc1.per = may_prevent and
	asc.act = write and
	asc.from = app1 and
	asc.to = ds and
	obj.parent = app2 and
	asc.per = shall_prevent
}

//Exist a area that conflict 195 and 086
assert check_195_086{
	some app1: NonTrusted, obj, obj1,obj2: OS_Object, app2: OS_App, asc: accessApp, asc1: accessObj, st:app2.ownSt, ds1:obj2.ownDS|
	(obj1 in Task or obj1 in Cate_2) and
		(obj2 in Task or obj2 in Cate_2) and
		obj1.parent = app1 and
		obj2.parent = app1 and
		(obj1 != obj2) and
		asc1.act = write and
		asc1.from = obj1 and
		asc1.to = ds1 and
		asc1.per = may_prevent and
	asc.act = write and
	asc.from = app1 and
	asc.to = st and
	obj.parent = app2 and
	asc.per = shall_prevent
}

//Exist a area that conflict 195 and 026
assert check_195_026{
	some app1: NonTrusted, obj1,obj2: OS_Object, app2: OS_App, asc: accessApp, asc1: accessObj, ds:app2.ownDS, ds1:obj2.ownDS|
	asc.act = read and
	asc.from = app1 and 
	asc.to = ds and 
	app1 != app2 and
	asc.per = may_prevent and
	(obj1 in Task or obj1 in Cate_2) and
		(obj2 in Task or obj2 in Cate_2) and
		obj1.parent = app1 and
		obj2.parent = app1 and
		(obj1 != obj2) and
		asc1.act = write and
		asc1.from = obj1 and
		asc1.to = ds1 and
		asc1.per = may_prevent 
}

//------------------------------------------------------------------------------------------
//Exist a area that conflict 208 and 087
assert check_208_087{
	some app: NonTrusted, obj,obj1, obj2: OS_Object, asc: accessApp,  ds:obj2.ownDS, st:obj2.ownDS|
	
		(obj1 in Task or obj1 in Cate_2) and
		(obj2 in Task or obj2 in Cate_2) and
		obj1.parent = app and
		obj2.parent = app and
		(obj1 != obj2) and
		asc.act = write and
		asc.from = obj1 and
		asc.to = st and
		asc.per = may_prevent
	 and
	(obj in Task or obj in Cate_2) and
		(asc.act = read or asc.act = write) and
		asc.from = obj and 
		asc.to = ds and
		asc.per = shall_permit
}

//Exist a area that conflict 208 and 356
assert check_208_196{
	some  app: NonTrusted, obj, obj1, obj2: OS_Object, asc: accessApp,  st:obj2.ownSt, st1:obj2.ownDS|
	(obj in Task or obj in Cate_2) and
		(asc.act = read or asc.act = write) and
		asc.from = obj and 
		asc.to = st and
		asc.per = shall_permit and
	(obj1 in Task or obj1 in Cate_2) and
		(obj2 in Task or obj2 in Cate_2) and
		obj1.parent = app and
		obj2.parent = app and
		(obj1 != obj2) and
		asc.act = write and
		asc.from = obj1 and
		asc.to = st1 and
		asc.per = may_prevent
}

//Exist a area that conflict 087 and 356
assert check_208_356{
	some app1: NonTrusted, obj, obj1, obj2: OS_Object, app2: OS_App, asc: accessApp, asc1: accessObj, st1:obj.ownSt, st:obj2.ownSt|
	asc.act = write and
	asc.from = app1 and
	asc.to = st and
	obj.parent = app2 and
	asc.per = shall_prevent and
	(obj1 in Task or obj1 in Cate_2) and
		(obj2 in Task or obj2 in Cate_2) and
		obj1.parent = app1 and
		obj2.parent = app1 and
		(obj1 != obj2) and
		asc1.act = write and
		asc1.from = obj1 and
		asc1.to = st1 and
		asc1.per = may_prevent
}

//Exist a area that conflict 208 and 355
assert check_208_355{
	some app1: NonTrusted, obj, obj1, obj2: OS_Object, app2: OS_App, asc: accessApp, asc1: accessObj, st:obj.ownSt, st1:obj.ownSt|
	(obj1 in Task or obj1 in Cate_2) and
		(obj2 in Task or obj2 in Cate_2) and
		obj1.parent = app1 and
		obj2.parent = app1 and
		(obj1 != obj2) and
		asc1.act = write and
		asc1.from = obj1 and
		asc1.to = st and
		asc1.per = may_prevent and
	asc.act = write and
	asc.from = app1 and
	asc.to = st1 and
	obj.parent = app2 and
	asc.per = shall_prevent
}

//Exist a area that conflict 208 and 207
assert check_208_207{
	some app1: NonTrusted, obj, obj1, obj2: OS_Object, app2: OS_App, asc: accessApp, asc1: accessObj, ds:app2.ownDS, st:obj2.ownSt|
	(obj1 in Task or obj1 in Cate_2) and
		(obj2 in Task or obj2 in Cate_2) and
		obj1.parent = app1 and
		obj2.parent = app1 and
		(obj1 != obj2) and
		asc1.act = write and
		asc1.from = obj1 and
		asc1.to = st and
		asc1.per = may_prevent and
	asc.act = write and
	asc.from = app1 and
	asc.to = ds and
	obj.parent = app2 and
	asc.per = shall_prevent
}

//Exist a area that conflict 208 and 086
assert check_208_086{
	some app1: NonTrusted, obj, obj1,obj2: OS_Object, app2: OS_App, asc: accessApp, asc1: accessObj, st:app2.ownSt, st1:obj2.ownSt|
	(obj1 in Task or obj1 in Cate_2) and
		(obj2 in Task or obj2 in Cate_2) and
		obj1.parent = app1 and
		obj2.parent = app1 and
		(obj1 != obj2) and
		asc1.act = write and
		asc1.from = obj1 and
		asc1.to = st1 and
		asc1.per = may_prevent and
	asc.act = write and
	asc.from = app1 and
	asc.to = st and
	obj.parent = app2 and
	asc.per = shall_prevent
}

//Exist a area that conflict 208 and 026
assert check_208_026{
	some app1: NonTrusted, obj1,obj2: OS_Object, app2: OS_App, asc: accessApp, asc1: accessObj, ds:app2.ownDS, st1:obj2.ownSt|
	asc.act = read and
	asc.from = app1 and 
	asc.to = ds and 
	app1 != app2 and
	asc.per = may_prevent and
	(obj1 in Task or obj1 in Cate_2) and
		(obj2 in Task or obj2 in Cate_2) and
		obj1.parent = app1 and
		obj2.parent = app1 and
		(obj1 != obj2) and
		asc1.act = write and
		asc1.from = obj1 and
		asc1.to = st1 and
		asc1.per = may_prevent 
}

//------------------------------------------------------------------------------------------
//Exist a area that conflict 087 and 356
assert check_087_196{
	some obj, obj2: OS_Object, asc: accessApp,  ds:obj2.ownDS, st:obj2.ownDS|
	(obj in Task or obj in Cate_2) and
		(asc.act = read or asc.act = write) and
		asc.from = obj and 
		asc.to = st and
		asc.per = shall_permit and
	(obj in Task or obj in Cate_2) and
		(asc.act = read or asc.act = write) and
		asc.from = obj and 
		asc.to = ds and
		asc.per = shall_permit
}

assert check_087_356{
	some app1: NonTrusted, obj: OS_Object, app2: OS_App, asc: accessApp, asc1: accessObj, ds:obj.ownDS, st:obj.ownDS|
	asc.act = write and
	asc.from = app1 and
	asc.to = st and
	obj.parent = app2 and
	asc.per = shall_prevent and
	(obj in Task or obj in Cate_2) and
		(asc1.act = read or asc1.act = write) and
		asc1.from = obj and 
		asc1.to = ds and
		asc1.per = shall_permit
}

//Exist a area that conflict 087 and 355
assert check_087_355{
	some app1: NonTrusted, obj: OS_Object, app2: OS_App, asc: accessApp, asc1: accessObj, ds:obj.ownDS, ds1:obj.ownDS|
	(obj in Task or obj in Cate_2) and
		(asc1.act = read or asc1.act = write) and
		asc1.from = obj and 
		asc1.to = ds1 and
		asc1.per = shall_permit and
	asc.act = write and
	asc.from = app1 and
	asc.to = ds and
	obj.parent = app2 and
	asc.per = shall_prevent
}

//Exist a area that conflict 087 and 207
assert check_087_207{
	some app1: NonTrusted, obj: OS_Object, app2: OS_App, asc: accessApp, asc1: accessObj, ds:obj.ownDS|
		(obj in Task or obj in Cate_2) and
		(asc1.act = read or asc1.act = write) and
		asc1.from = obj and 
		asc1.to = ds and
		asc1.per = shall_permit and
	asc.act = write and
	asc.from = app1 and
	asc.to = ds and
	obj.parent = app2 and
	asc.per = shall_prevent
}

//Exist a area that conflict 087 and 086
assert check_087_086{
	some app1: NonTrusted, obj, obj1: OS_Object, app2: OS_App, asc: accessApp, asc1: accessObj, st:obj.ownSt, ds:obj1.ownDS|
	(obj1 in Task or obj1 in Cate_2) and
		(asc1.act = read or asc1.act = write) and
		asc1.from = obj1 and 
		asc1.to = ds and
		asc1.per = shall_permit and
	asc.act = write and
	asc.from = app1 and
	asc.to = st and
	obj.parent = app2 and
	asc.per = shall_prevent
}

//Exist a area that conflict 087 and 026
assert check_087_026{
	some app1: NonTrusted, obj: OS_Object, app2: OS_App, asc: accessApp, asc1: accessObj, ds:app2.ownDS, st:obj.ownSt|
	asc.act = read and
	asc.from = app1 and 
	asc.to = ds and 
	app1 != app2 and
	asc.per = may_prevent and
	(obj in Task or obj in Cate_2) and
		(asc1.act = read or asc1.act = write) and
		asc1.from = obj and 
		asc1.to = st and
		asc1.per = shall_permit
}

//------------------------------------------------------------------------------------------
//Exist a area that conflict 196 and 356
assert check_196_356{
	some app1: NonTrusted, obj: OS_Object, app2: OS_App, asc: accessApp, asc1: accessObj, st1:obj.ownSt|
	asc.act = write and
	asc.from = app1 and
	asc.to = st1 and
	obj.parent = app2 and
	asc.per = shall_prevent and
	(obj in Task or obj in Cate_2) and
		(asc1.act = read or asc1.act = write) and
		asc1.from = obj and 
		asc1.to = st1 and
		asc1.per = shall_permit
}

//Exist a area that conflict 196 and 355
assert check_196_355{
	some app1: NonTrusted, obj: OS_Object, app2: OS_App, asc: accessApp, asc1: accessObj, ds:obj.ownDS, st:obj.ownSt|
	(obj in Task or obj in Cate_2) and
		(asc1.act = read or asc1.act = write) and
		asc1.from = obj and 
		asc1.to = st and
		asc1.per = shall_permit and
	asc.act = write and
	asc.from = app1 and
	asc.to = ds and
	obj.parent = app2 and
	asc.per = shall_prevent
}

//Exist a area that conflict 196 and 207
assert check_196_207{
	some app1: NonTrusted, obj: OS_Object, app2: OS_App, asc: accessApp, asc1: accessObj, ds:app2.ownDS, st:obj.ownSt|
		(obj in Task or obj in Cate_2) and
		(asc1.act = read or asc1.act = write) and
		asc1.from = obj and 
		asc1.to = st and
		asc1.per = shall_permit and
	asc.act = write and
	asc.from = app1 and
	asc.to = ds and
	obj.parent = app2 and
	asc.per = shall_prevent
}

//Exist a area that conflict 196 and 086
assert check_196_086{
	some app1: NonTrusted, obj, obj1: OS_Object, app2: OS_App, asc: accessApp, asc1: accessObj, st:app2.ownSt, st1:obj1.ownSt|
	(obj1 in Task or obj1 in Cate_2) and
		(asc1.act = read or asc1.act = write) and
		asc1.from = obj1 and 
		asc1.to = st1 and
		asc1.per = shall_permit and
	asc.act = write and
	asc.from = app1 and
	asc.to = st and
	obj.parent = app2 and
	asc.per = shall_prevent
}

//Exist a area that conflict 196 and 026
assert check_196_026{
	some app1: NonTrusted, obj: OS_Object, app2: OS_App, asc: accessApp, asc1: accessObj, ds:app2.ownDS, st:obj.ownSt|
	asc.act = read and
	asc.from = app1 and 
	asc.to = ds and 
	app1 != app2 and
	asc.per = may_prevent and
	(obj in Task or obj in Cate_2) and
		(asc1.act = read or asc1.act = write) and
		asc1.from = obj and 
		asc1.to = st and
		asc1.per = shall_permit
}

//------------------------------------------------------------------------------------------
//Exist a area that conflict 026 and 356
assert check_356_355{
	some app1: NonTrusted, obj: OS_Object, app2: OS_App, asc: accessApp, ds:obj.ownDS, st:obj.ownSt|
	asc.act = write and
	asc.from = app1 and
	asc.to = st and
	obj.parent = app2 and
	asc.per = shall_prevent and
	asc.act = write and
	asc.from = app1 and
	asc.to = ds and
	obj.parent = app2 and
	asc.per = shall_prevent
}

//Exist a area that conflict 026 and 356
assert check_356_207{
	some app1: NonTrusted, obj: OS_Object, app2: OS_App, asc: accessApp, ds:obj.ownDS, st:app2.ownSt|
	asc.act = write and
	asc.from = app1 and 
	asc.to = st and 
	app1 != app2 and
	asc.per = may_prevent and
	asc.act = write and
	asc.from = app1 and
	asc.to = ds and
	obj.parent = app2 and
	asc.per = shall_prevent
}

//Exist a area that conflict 086 and 355
assert check_356_086{
	some app1: NonTrusted, obj: OS_Object, app2: OS_App, asc: accessApp, st:app2.ownSt|
	(asc.act = read or asc.act = write) and
	asc.from = app2 and 
	asc.to = app2.ownDS and
	asc.per = shall_permit and
	asc.act = write and
	asc.from = app1 and
	asc.to = st and
	obj.parent = app2 and
	asc.per = shall_prevent
}

//Exist a area that conflict 026 and 355
assert check_356_026{
	some app1: NonTrusted, obj: OS_Object, app2: OS_App, asc: accessApp, ds:app2.ownDS, st:obj.ownSt|
	asc.act = read and
	asc.from = app1 and 
	asc.to = ds and 
	app1 != app2 and
	asc.per = may_prevent and
	asc.act = write and
	asc.from = app1 and
	asc.to = st and
	obj.parent = app2 and
	asc.per = shall_prevent
}
//------------------------------------------------------------------------------------------

//Exist a area that conflict 207 and 355
assert check_355_207{
	some app1: NonTrusted, obj: OS_Object, app2: OS_App, asc: accessApp, ds:obj.ownDS|
	asc.act = write and
	asc.from = app1 and 
	asc.to = ds and 
	app1 != app2 and
	asc.per = may_prevent and
	asc.act = write and
	asc.from = app1 and
	asc.to = ds and
	obj.parent = app2 and
	asc.per = shall_prevent
}

//Exist a area that conflict 086 and 355
assert check_355_086{
	some app1: NonTrusted, obj: OS_Object, app2: OS_App, asc: accessApp, ds:app2.ownDS|
	(asc.act = read or asc.act = write) and
	asc.from = app2 and 
	asc.to = app2.ownDS and
	asc.per = shall_permit and
	asc.act = write and
	asc.from = app1 and
	asc.to = ds and
	obj.parent = app2 and
	asc.per = shall_prevent
}

//Exist a area that conflict 026 and 355
assert check_355_026{
	some app1: NonTrusted, obj: OS_Object, app2: OS_App, asc: accessApp, ds:app2.ownDS|
	asc.act = read and
	asc.from = app1 and 
	asc.to = ds and 
	app1 != app2 and
	asc.per = may_prevent and
	asc.act = write and
	asc.from = app1 and
	asc.to = ds and
	obj.parent = app2 and
	asc.per = shall_prevent
}

//------------------------------------------------------------------------------------------
//Exist a area that conflict 026 and 086
assert check_026_086{
	some app1: NonTrusted, app, app2: OS_App, asc, asc1: accessApp, ds:app2.ownDS|
	asc.act = read and
	asc.from = app1 and 
	asc.to = ds and 
	app1 != app2 and
	asc.per = may_prevent and
	(asc1.act = read or asc1.act = write) and
	asc1.from = app and 
	asc1.to = app.ownDS and
	asc1.per = shall_permit
}

//------------------------------------------------------------------------------------------
//Exist a area that conflict 207 and 086
assert check_207_086{
	some app1: NonTrusted, app, app2: OS_App, asc, asc1: accessApp, ds:app2.ownDS|
	asc.act = write and
	asc.from = app1 and 
	asc.to = ds and 
	app1 != app2 and
	asc.per = may_prevent and
	(asc1.act = read or asc1.act = write) and
	asc1.from = app and 
	asc1.to = app.ownDS and
	asc1.per = shall_permit
}

//Exist a area that conflict 207 and 026
assert check_207_026{
	some app1: NonTrusted, app2: OS_App, asc: accessApp, ds:app2.ownDS|
	asc.act = write  and
	asc.from = app1 and 
	asc.to = ds and 
	app1 != app2 and
	asc.per = may_prevent and
		asc.act = read and
		asc.from = app1 and 
		asc.to = ds and 
		app1 != app2 and
		asc.per = may_prevent
}

check check_195_208
check check_195_026
check check_195_086
check check_195_207
check check_195_355
check check_195_356
check check_195_196
check check_195_087
check check_208_026
check check_208_086
check check_208_207
check check_208_355
check check_208_356
check check_208_196
check check_208_087 for 5
check check_087_026
check check_087_356
check check_087_355
check check_087_207
check check_087_086
check check_087_196
check check_196_086
check check_196_207
check check_196_355
check check_196_356
check check_196_026
check check_356_355
check check_356_086
check check_356_207
check check_356_026
check check_355_086
check check_355_207
check check_355_026
check check_207_026 for 5 but 2 OS_App
check check_207_086
check check_026_086
