open util/boolean
open util/integer

-- The username used by a User or a Third-Party --
sig Username{}

-- The SSN of a User --
sig SSN{}

-- For male User, male = TRUE and female = FALSE. Otherwise, for female User, female = TRUE and male = FALSE--
sig Gender{
	male: one Bool,
	female: one Bool
}
{(male.isTrue and female.isFalse) or (female.isTrue and male.isFalse)}

-- The acceptedRequests is a set of Single Requests that a specific user has accepted, while pendantRequests refers to all the pending requests of a specific user --
-- A request is accepted to give the authorization to a Third-Party to get access to his own latest personal data --
sig User{
	username: one Username,
	ssn: one SSN,
	acceptedRequests: set SingleReq,
	pendantRequests: set SingleReq,
	location: one Location,
	data: one PersonalData,
	age: one Int,
	gender: one Gender,
	automatedSos: lone AutomatedSOS
}
{age>=0}


sig Location{
	-- latitude --
	lat: one Int,
	-- longitude --
	long: one Int
}
-- { lat >= -90 and lat <= 90 and long>= -180 and long<= 180 }
{lat >= -3 and lat<= 3 and long>= -6 and long<= 6}


sig ThirdP{
	username: one Username,
	requests: set Request
}

 
abstract sig Request{
	accepted: one Bool,
	subscribed: one Bool
}
{subscribed.isTrue implies accepted.isTrue}


sig SingleReq extends Request{
	user: one User
}

-- left, right, top and bottom are the sides of the area concerning a Group request --
sig SquareArea{
	left: one Int,
	right: one Int,
	top: one Int,
	bottom: one Int
}
-- { left<=right and top<=bottom and left>= -90 and right <= 90 and top>= -180 and bottom<= 180 } --
{left<=right and top<=bottom and left>= -6 and right <= 6 and top>= -3 and bottom<= 3}

-- Two limits concerning the Users’ age involved in a group Request --
sig AgeRange{
	minAge: one Int,
	maxAge: one Int
}
{minAge <= maxAge and minAge>=0}

-- a group 
sig GroupReq extends Request{
	data: set PersonalData,
	square: lone SquareArea,
	age: lone AgeRange,
	gender: lone Gender
}
{
	(square != none or age!=none or gender!=none) and (accepted.isFalse implies data = none)
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

-- GENDER CONNECRION USER E GROUP --
fact genderConnectionUser{
	(all disj g1,g2: Gender | g1.male!=g2.male) and #Gender = 2
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
	all r: Request | one tp: ThirdP | r in tp.requests
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
		)and
		(g.gender = none or
			(all d: g.data | one u: User | u.data = d and 
				(u.gender.male = g.gender.male)
			)
		)
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
			(u.data.min_pressure>5 or u.data.min_pressure<2 or u.data.max_pressure>6 or u.data.max_pressure<3  or u.data.bpm<2 or u.data.bpm>6) implies
				u.automatedSos.emergency.isTrue
				else u.automatedSos.emergency.isFalse
	)
}


pred healthUser[u:User]{
	one p:PersonalData | u.data = p and u.automatedSos != none and (p.max_pressure = 3 and p.min_pressure = 2 and p.bpm =3)
}

pred needEmergency[u:User]{
	one p:PersonalData | u.data = p and u.automatedSos != none and p.max_pressure = 2
}

pred callAmbulance[u1: User, u2: User]{
	//preconditions
	healthUser[u1]
	needEmergency[u2]
	//postconditions
	u1.automatedSos.emergency.isFalse
	u2.automatedSos.emergency.isTrue	
}

-------------------------
pred acceptedReqInAcceptedList[s:SingleReq]{
	one u: User | s in u.acceptedRequests
}

pred pendingtReqInPendingList[s:SingleReq]{
	one u: User | s in u.pendantRequests
}

pred singleReqWellPlaced[s1: SingleReq, s2: SingleReq]{
	//pre-conditions
	s1.accepted.isTrue
	s2.accepted.isFalse
	//post-conditions
	acceptedReqInAcceptedList[s1]
	pendingtReqInPendingList[s2]
}

--run callAmbulance
--run singleReqWellPlaced

fact dhs{
	#ThirdP > 2 and #User > 2
	--#SingleReq > 2
	--#GroupReq > 2
}

pred show{

	
}

run show for 7
