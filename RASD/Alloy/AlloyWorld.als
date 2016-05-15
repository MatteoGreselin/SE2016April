module SmartCityService

//-------SIGNATURES-------//

abstract sig Person{}

abstract sig Superuser{}

abstract sig System{}
{#System = 1}

sig Guest extends Person{
		seeTrafficSituation: set TrafficSituation,
		seeParkingSituation: set ParkingSituation,
		seeProgrammedEvents: set ProgrammedEvents,
		activateHospitalEmergency: set HospitalEmergency,
}

sig TrafficSituation {
		sender: lone Guest,
		receiver: one System,
		updateBy: one PublicTransportCompany,
		manageBy: one TrafficLights
}
{#TrafficSituation=1}

sig ParkingSituation {
		forwardTo: one System,
		updatesBy: one ParkingSystem
}

sig ProgrammedEvents {
		forwardTo: one System,
		updateBy: one CityAdministration
}
{#ProgrammedEvents = 1}

sig HospitalEmergency {
		activatedBy: one Guest,
		forwardTo: one System,
		updateInformationBy: one Hospital,
} 

sig User extends Guest{
		reserve: set ParkingReservation
}

sig ParkingReservation{
		createsBy: one User,
		forwardTo: one ParkingSystem
}

sig CityAdministration extends Superuser{
		manages: set TrafficLights,
		sees: set GeneralReports,
		sends: set AdminNotification,
}
{#CityAdministration = 1}

sig TrafficLights{}
{#TrafficLights = 1}

sig GeneralReports{}
{#GeneralReports = 1}

sig CityAdministrationApproval{
		responseY: set ExceptionalNotification,
		responseN: set ExceptionalNotificationDenied
}

sig ExceptionalNotification{
		sendBy: one PublicTransportCompany,
		forwardTo: one User
}

sig ExceptionalNotificationDenied{
		forwardTo: one PublicTransportCompany
}

sig AdminNotification{

		createdBy: one CityAdministration,
		forwardTo: one User
}

sig Hospital extends Superuser{
		createsNew: set HelpRequest,
		manages: set HospitalSpecializations,
		updates: set Queues
}
{#Hospital > 1}

sig HelpRequest{
		createsBy: one Hospital,
		insertsBy: one Police,
		forwardTo: one System
}

sig HospitalSpecializations{
		updatesBy: one Hospital,
		forwardTo: one System
}

sig Queues{
		updatesBy: one Hospital,
		forwardTo: one System
}

sig Police extends Superuser{
		createsNew: set HelpRequest
}
{#Police != 1}

sig PublicTransportCompany extends Superuser{
		updates: set PublicTransportPosition,
		sends: set ExceptionalNotificationReq
}
{#PublicTransportCompany = 1}

sig PublicTransportPosition{
		updateBy: one PublicTransportCompany,
		forwardTo: one System
}
{#PublicTransportPosition=1}

sig ExceptionalNotificationReq{
		sentsBy: one PublicTransportCompany,
		forwardTo: one CityAdministrationApproval
}

sig ParkingSystem extends Superuser{
		updates: set ParkingSituation,		
}
{#ParkingSystem > 0}


//-------FACTS-------//

//Each person could activates his/her personal hospital emergency
fact guestRestriction{
		all g: Guest | #g.activateHospitalEmergency = 1
		all h: HospitalEmergency | #h.activatedBy = 1
		no disj g1, g2: Guest | g1.activateHospitalEmergency = g2.activateHospitalEmergency
		no disj h1, h2: HospitalEmergency | h1.activatedBy = h2.activatedBy
}

//Each user could be reserve only on car park
fact userRestriction{
		all u: User | #u.reserve <= 1
		no disj u1,u2: User| u1.reserve =u2.reserve
		no disj p1,p2: ParkingReservation | p1.createsBy = p2.createsBy
}

//Administration notification must arrive to all users
fact cityAdministrationNotifForAllUsers{
		all u: User, a: AdminNotification | a.forwardTo = u
}

//Each car park must have its parkink availability situation
fact parkingSystemAndSituation{
		all p: ParkingSystem, ps: ParkingSituation | #p = #ps
		no disj ps1, ps2:ParkingSituation | ps1.updatesBy = ps2.updatesBy
		no disj ps1, ps2:ParkingSystem | ps1.updates = ps2.updates
}

//Each hospital must have its queues situation and its specializations
fact HospitalQueuesAndSpecializations{
		all h: Hospital, q:Queues | #h = #q and h= q.updatesBy
		all h: Hospital, hs:HospitalSpecializations | #h >= #hs and h = hs.updatesBy
		no disj q1,q2: Queues | q1.updatesBy =q2.updatesBy
		no disj hs1, hs2:HospitalSpecializations | hs1.updatesBy = hs2.updatesBy
}

//Each exceptional notification request must have its own response
fact exceptionalNotificationPermissions{
		all c: CityAdministrationApproval, e: ExceptionalNotificationReq | #c = #e
		all c:CityAdministrationApproval | #c.responseY + #c.responseN = 1
		no disj c1, c2 : CityAdministrationApproval | c1.responseY = c2.responseY 
				or c1.responseN = c2.responseN
}

//-------PREDICATES-------//

pred generateWorld{}

run generateWorld for 3
