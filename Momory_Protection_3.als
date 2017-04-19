module mem_pro_3

// Objects
sig OS_App{}
sig OS_Obj extends OS_App{}			
sig Tasks, ISRs extends OS_Obj{}		// two diff subsets of Object
sig Cate_1, Cate_2 extends ISRs{}		// two diff subsets of Category.
sig Trusted, NonTrusted extends OS_App{}

//Memory
abstract sig Memory{}		// no elements
sig Data_Sections, Stacks extends Memory{}

//System status
sig status{}
one sig initStt, may_prevent, may_permit, shall_prevent, 
shall_permit extends status{}

sig action{}
one sig initAct, read, write extends action{}
/*
sig State{
	act: action,
	stt: status
}
*/
//Ownership
sig App_Data{
	rel: OS_App one -> lone Data_Sections
}

sig Obj_Data{
	rel: OS_Obj one -> one Data_Sections
}

sig Obj_Stack{
	rel: OS_Obj one -> one Stacks
}

pred show(){
}

run show for 3

