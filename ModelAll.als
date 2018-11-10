open util/boolean
open util/integer

sig Username{}
sig SSN{}

sig User{
	username: one Username,
	ssn: one SSN,
	acceptedRequests: set SingleReq,
	pendantRequests: set SingleReq,
	location: one Location,
	data: one PersonalData,
	age: one Int,
	automatedSos: lone AutomatedSOS
}
{age>0}



sig Location{
	lat: one Int,
	long: one Int
}
{lat >= -3 and lat<= 3 and long>= -6 and long<= 6}

sig ThirdP{
	username: one Username,
	requests: set Request
}


abstract sig Request{
	accepted: one Bool
}

sig SingleReq extends Request{
	user: one User
}

sig SquareArea{
	left: one Int,
	right: one Int,
	top: one Int,
	bottom: one Int
}
-- valori reali --
{left<=right and top<=bottom and left>= -6 and right <= 6 and top>= -3 and bottom<= 3}


sig AgeRange{
	minAge: one Int,
	maxAge: one Int
}
{minAge <= maxAge and minAge>0}

sig GroupReq extends Request{
	data: set PersonalData,
	square: lone SquareArea,
	age: lone AgeRange
}

sig PersonalData{
	max_pressure: one Int,
	min_pressure: one Int,
	bpm: one Int
}
{min_pressure> 0 and min_pressure< max_pressure and bpm>0}

sig AutomatedSOS{
	emergency: one Bool
}

-- utenti distinti--
fact distinctUser{
	all disj u1,u2: User | u1.username != u2.username and u1.ssn != u2.ssn
}

fact distinctReq{
	all disj tp1,tp2: ThirdP | (tp1.requests & tp2.requests) = none
}

-- username appartiene o a user o 3p --
fact UsernameAreConnected{
	all u: Username | u in ( User.username + ThirdP.username)
}

/*
fact Usaefas{
	#Username = #(User.username + ThirdP.username )
}
*/

-- ssn collecati a use
fact ssnConnectionUser{
	all s: SSN | one u: User | u.ssn = s
}

-- location collecati a user
fact locationConnectionUser{
	all l: Location | one u: User | u.location = l
}


-- area collecati a grouReq
fact squareAreaConnectionGroupR{
	all s: SquareArea | one gr: GroupReq | s=gr.square
}

-- range age collecati a grouReq
fact ageConnectionGroupR{
	all a: AgeRange | one gr: GroupReq | a=gr.age
}


-- TP distinti--
fact distinctTp
{all disj tp1,tp2: ThirdP | tp1.username != tp2.username }

-- Usernamen--
fact  distinctUsername{
	all u:User, tp:ThirdP | u.username != tp.username
}

-- persoanl data per user --
fact PersonalDataUserConnection {
	all p: PersonalData | one u: User | p=u.data
}

-- request per third--
fact RequestThirdPConnection {
--	all r: Request | one tp: ThirdP | r in tp.requests
	all r: Request | r in ThirdP.requests
}

-- Group of request must satisfy ... -
fact validNumGroupRequest{
	all g: GroupReq |  
		(#g.data >5) implies g.accepted.isTrue else g.accepted.isFalse
}

fact validDataGroupReq{
	all g: GroupReq |
		(g.square = none or
			(all d: g.data | one u: User | u.data = d and 
				(u.location.lat<=g.square.bottom and u.location.lat>=g.square.top and u.location.long<=g.square.right and u.location.lat>=g.square.left)
			 ) 
		) and
		(g.age = none or
			(all d: g.data | one u: User | u.data = d and 
				(u.age>=g.age.minAge and u.age<=g.age.maxAge)
			 ) 
		)	
}

fact validGroupReq{
	all g: GroupReq | (g.square != none or g.age!=none) and (g.accepted.isFalse implies g.data = none)
}


-- utente ha accettato --
fact validAcceptedRequest{
	(all s:SingleReq |
		 s.accepted.isTrue implies one u: User | s in u.acceptedRequests
	)
	and
	(all u: User |
		all a: u.acceptedRequests | a.accepted.isTrue
	) 

}

-- AutomatedSOS collegati a singolo user --
fact SosUserConnection {
	all a: AutomatedSOS | one u: User | a=u.automatedSos
}

-- Single Request associate correttamente agli user --
fact SingleRequestUserConnection {
	all u: User| all r: (u.acceptedRequests + u.pendantRequests) | r.user = u
}

fact validPendantRequest{
	(all s:SingleReq |
		 s.accepted.isFalse implies one u: User | s in u.pendantRequests
	)
	and
	(all u: User |
		all a: u.pendantRequests | a.accepted.isFalse
	) 

}

-- valori reali --
fact emergencyCall{
	(all u: User |
		u.automatedSos = none or
			(u.data.min_pressure>5 or u.data.min_pressure<3 or u.data.max_pressure>6 or u.data.max_pressure<2  or u.data.bpm<2 or u.data.bpm>6) implies
				u.automatedSos.emergency.isTrue
				else u.automatedSos.emergency.isFalse
	)
}


pred show{
/*
	#ThirdP > 0
	#User > 0
	#SingleReq > 0
	#GroupReq > 0
*/
}

run show for 5
