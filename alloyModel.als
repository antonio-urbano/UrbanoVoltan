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
-- automatedSos indicates if a User is subscribed to the automatedSOS service --
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
-- age cannot be negative --
{age>=0 and (all p: pendantRequests | p.accepted.isFalse) and (all a: acceptedRequests | a.accepted.isTrue) }


sig Location{
	-- latitude --
	lat: one Int,
	-- longitude --
	long: one Int
}
-- { lat >= -90 and lat <= 90 and long>= -180 and long<= 180 }
{lat >= -3 and lat<= 3 and long>= -6 and long<= 6}

-- requests can be accepted or not --
sig ThirdP{
	username: one Username,
	requests: set Request
}

 
abstract sig Request{
	accepted: one Bool,
	subscribed: one Bool
}
-- a request can have a subscription only if it is an accepted request --
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


-- a group request consists of a set of Personal Data and some constraints used for make the request --
sig GroupReq extends Request{
	data: set PersonalData,
	square: lone SquareArea,
	age: lone AgeRange,
	gender: lone Gender
}
-- a group request exists (exists a set of Personal Data) only if it is accepted
-- A group request is accepted only if there is at least one costraint (the square Area, the age Range or the gender)
{
	(square != none or age!=none or gender!=none) and (accepted.isFalse implies data = none)
}

-- data measured and collected --
sig PersonalData{
	max_pressure: one Int,
	min_pressure: one Int,
	bpm: one Int
}
{min_pressure> 0 and min_pressure< max_pressure and bpm>0}

-- if emergency = TRUE, the health status of an User of the AutomatedSOS service is critical (at least one of the personal data cross the related treshold value) --
sig AutomatedSOS{
	emergency: one Bool
}



-- FACT --

-- Considering two distinct User, they can never have the same username or the same SSN --
fact distinctUser{
	all disj u1,u2: User | u1.username != u2.username and u1.ssn != u2.ssn
}

-- Each request can belong to only one third Party, so there will never be a request concerning two different third-party --
fact distinctReq{
	all disj tp1,tp2: ThirdP | (tp1.requests & tp2.requests) = none
}

-- Each username belong to either a User or a Third Party. There will never be an username which no belong to a Customer --
fact UsernameAreConnected{
	all u: Username | u in ( User.username + ThirdP.username)
}


-- Each SSN belong to one and only one User --
fact ssnConnectionUser{
	all s: SSN | one u: User | u.ssn = s
}

-- Each Location belong to one and only one User --
fact locationConnectionUser{
	all l: Location | one u: User | u.location = l
}


-- Each squareArea belong to one and only one GroupRequest --
fact squareAreaConnectionGroupR{
	all s: SquareArea | one gr: GroupReq | s=gr.square
}

-- Each ageRange belong to one and only one GroupRequest --
fact ageConnectionGroupR{
	all a: AgeRange | one gr: GroupReq | a=gr.age
}

-- A gender constraint can Male or Female --
fact genderConnectionUser{
	(all disj g1,g2: Gender | g1.male!=g2.male) and #Gender = 2
}

-- Considering two distinct Third Parties, they can never have the same username --
fact distinctTp
{all disj tp1,tp2: ThirdP | tp1.username != tp2.username }

-- Considering a User and a Third Party, they can never have the same username --
fact  distinctUsername{
	all u:User, tp:ThirdP | u.username != tp.username
}

-- Each personal data belong to a specific User --
fact PersonalDataUserConnection {
	all p: PersonalData | one u: User | p=u.data
}

-- -- Each request belong to a specific Third Party --
fact RequestThirdPConnection {
	all r: Request | one tp: ThirdP | r in tp.requests
}

-- TrackMe will	accept any	request  for which the number of	 individuals	 whose data satisfy the request is higher than 1000
fact validNumGroupRequest{
	all g: GroupReq |  
		(#g.data >5) implies g.accepted.isTrue else g.accepted.isFalse
}

-- a groupRequest is valid if each user's location of the request is within the square area speciified in the group request OR
-- if the user's age of the request is within the two limits of the age Range OR
-- if The gender types of a Group request and the corresponding Peronal data must match
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



-- If a single request is accepted by a user, it belong to a acceptedRequests list of that specific user --
fact validAcceptedRequest{
	(all s:SingleReq |
		 s.accepted.isTrue implies one u: User | s in u.acceptedRequests
	) 

}

-- If a single request is NOT accepted by a user, it belong to a pendantRequests list of that specific user --
fact validPendantRequest{
	(all s:SingleReq |
		 s.accepted.isFalse implies one u: User | s in u.pendantRequests
	)
}

-- Each AutomatedSOS belong to only one User -- 
fact SosUserConnection {
	all a: AutomatedSOS | one u: User | a=u.automatedSos
}

-- all the Single request (accepted or not) of a specific user must belong to at least one of the two lists of requests of that specific user (acceptedRequests or pendantRequests) --
fact SingleRequestUserConnection {
	all u: User| all r: (u.acceptedRequests + u.pendantRequests) | r.user = u
}



-- if there is the AutomatedSOS service and at least one of the personal data cross the related treshold value, there will be an emergency notification, 
-- otherwise there will not be  any emergency notification--
fact emergencyCall{
	(all u: User |
		u.automatedSos = none or
			(u.data.min_pressure>5 or u.data.min_pressure<2 or u.data.max_pressure>6 or u.data.max_pressure<3  or u.data.bpm<2 or u.data.bpm>6) implies
				u.automatedSos.emergency.isTrue
				else u.automatedSos.emergency.isFalse
	)
}


-- PREDICATES --

-- Health Status of the User u is good (all the Personal Data values DO NOT cross threshold values) --
-- User u has actived AutomatedSos service --
pred healthyUser[u:User]{
	one p:PersonalData | u.data = p and u.automatedSos != none and (p.max_pressure = 3 and p.min_pressure = 2 and p.bpm =3)
}

-- Health Status of the User u is NOTgood (one of the Personal Data values cross the corresponding threshold value) --
-- User u has actived AutomatedSos service --
pred needEmergency[u:User]{
	one p:PersonalData | u.data = p and u.automatedSos != none and p.max_pressure = 2
}

-- User u1 is in healthy condition, so NO emergency call is necessary
--Otherwise User u2 has bad health conditions, so an emergency call is necessary
pred callAmbulance[u1: User, u2: User]{
	//preconditions
	healthyUser[u1]
	needEmergency[u2]
	//postconditions
	u1.automatedSos.emergency.isFalse
	u2.automatedSos.emergency.isTrue	
}

-------------------------

-- The single request s is an accepted request present in the acceptedRequests list of an User u --
pred acceptedSingleReqInAcceptedList[s:SingleReq]{
	one u: User | s in u.acceptedRequests
}

-- The single request s is a pending request present in the pendantRequests list of an User u --
pred pendingSingleReqInPendingList[s:SingleReq]{
	one u: User | s in u.pendantRequests
}

-- If a request has been accepted, it must be in an acceptedRequests list, otherwise it must be in a pendantRequests list--
pred singleReqWellPlaced[s1: SingleReq, s2: SingleReq]{
	//pre-conditions
	s1.accepted.isTrue
	s2.accepted.isFalse
	//post-conditions
	acceptedSingleReqInAcceptedList[s1]
	pendingSingleReqInPendingList[s2]
}

--run callAmbulance
--run singleReqWellPlaced

fact dhs{
	
}

pred show{
	#ThirdP > 2
	#User > 2
	#SingleReq > 2
	#GroupReq > 2
}

run show for 7
