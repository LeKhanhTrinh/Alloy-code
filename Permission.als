module carreer
/**
Each kind of staff might be prevented (or permitted) from accessing Source
*/

// Define kinds of Staffs, Source and Status
abstract sig Staff{}
one sig Engineer, Doctor, Assistant extends Staff{}

abstract sig Source{}
one sig TopSecret, Public extends Source{}

abstract sig Actions{}
one sig Read, Write extends Actions{}

abstract sig Status{}
one sig Prevent, Permit extends Status{}

// Define a request
sig Request{
	from: Staff,
	to: Source,
	act: Actions,
	per: Request -> Status
}

// If request A then status B
/*
sig Permission{
	per: Request -> Status
}*/

// Constraints of system
fact {
	/*
	//All Engineers are prevented from writing Public Source
	all e:Engineer, p:Public, req:Request, pr:Permission |
		req.from = e and
		req.to = p and
		req.act = Write and
		pr.per[Request] = Prevent

	//All Doctors are permitted to writing TopSecret Source
	all d:Doctor, ts:TopSecret, req:Request, pr:Permission |
		req.from = d and
		req.to = ts and
		req.act = Write and
		pr.per[Request] = Permit
*/
	all req:Request |
		(all e: Engineer, p: Public | RequestOfEngineers[e, p, req]) implies req.per[Request] = Prevent

	all req:Request|
		(all d:Doctor, t: TopSecret | RequestOfDoctor[d, t, req]) implies req.per[Request] = Permit
}

/**
-Purpose: Assume we have two Constrants: A1 -> B1, A2 -> B2
I want to check the existence of the inconsistency between two constraint, so I will create an assertion that
/forAll staff, source, action, status. Request(A1) and Request(A2) and B1 != B2
If it has a counter example it means that I have inconsistency 

- Process:
 + Function Request: assign each value a request
 + Function Permiss: from a request, return the permission 

- Function RequestOfEngineer: Return the request: Engineer wants to Read Public source.
- Function PermissionOfEng: Return the permission: Prevent
*/
//Functions
//Return the request: Engineer wants to Read Public source. (DOESN'T WORK)

pred RequestOfEngineers[e:Engineer, p:Public, req:Request]{
	req.from = e
	req.to = p
	req.act = Write
}


pred RequestOfDoctor[d:Doctor, t:TopSecret, req:Request]{
	req.from = d
	req.to = t
	req.act = Write
}
/*
pred RequestOfEngineers[e:Engineer, p:Public, req:Request]{
	req.from = e
	req.to = p
	req.act = Write
}

pred PermissionOfEngineer[req:Request, prm:Permission]{
    (all e: Engineer, p: Public | RequestOfEngineers[e, p, req]) implies
        prm.per[Request] = Prevent
}

pred RequestOfDoctor[d:Doctor, t:TopSecret, req:Request]{
	req.from = d
	req.to = t
	req.act = Write
}

pred PermissionOfDoctor[req:Request, prm:Permission]{
    (all d:Doctor, t: TopSecret | RequestOfDoctor[d, t, req]) implies
        prm.per[Request] = Permit
}

*/
assert testPOE{
	all d:Doctor, t: TopSecret , e: Engineer, p: Public, req, reqD:Request |
		RequestOfEngineers[e, p, req] and RequestOfDoctor[d, t, reqD] and req.per[Request] != reqD.per[Request]

}

check testPOE
