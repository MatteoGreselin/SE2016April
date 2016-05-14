
abstract sig User {} 

sig VisitorUser extends User {}

sig PassengerUser extends User {

	send: set Request,
	banned: lone Ban

}

one sig Ban {}

one sig PotentialSharableRide{}

sig TaxiDriverUser extends User {	

	send: set TaxiConfirmation,
	enqueuedInto: lone Queue,
	has: one RideSchedule,
	availability: one Boolean,

}

sig RideSchedule{

	associatedTo: one TaxiDriverUser,
	updatedBy: set TaxiConfirmation

}

sig Destination{}

sig Origin{}

abstract sig Request{

	askFor: one TaxiConfirmation,
	sendedBy: one PassengerUser,
	startsFrom: one Origin,
	endsIn: one Destination,
	sharingAvailable: lone PotentialSharableRide

}


sig TaxiConfirmation{
	
		camesFrom: one TaxiDriverUser,
		neededBy: one Request,
		generates: one SystemAnswer,
		updates: one RideSchedule

}

sig InstantReq extends Request {	}

sig BookingReq extends Request {

	generates: one BookTakenInChargeMSG

 }

sig BookTakenInChargeMSG {

	generatedBy: one BookingReq

}

sig SystemAnswer{

	generatedBy: one Request,
	associated: one TaxiConfirmation
	
}

sig Queue{

	contains: set TaxiDriverUser,
	associatedTo: one Zone

}

sig Zone {

	haveOne: one Queue

}

abstract sig Boolean {}

one sig Available extends Boolean {}
one sig NotAvailable extends Boolean {}

//Fact eliceted from class diagram, assumptions and requirements
	
//Request relations: 

	fact eachReqHasOnePUser{
		all r: Request , p: PassengerUser | r in p. send <=> p in r. sendedBy
	}

	fact eachRequestNeedATaxiConfirmation{
		all r: Request , t: TaxiConfirmation | r in t. neededBy  <=> t in r. askFor
	}
	
	// A booking taken in charge generates MSG 

	fact BookingMSG {
		all b: BookingReq , m: BookTakenInChargeMSG   | b in m. generatedBy   <=> m in b. generates
	}
	
//Taxi Confirmation relations:

	fact eachTaxiConfIsSendedByATaxiDriverUser{
		all t: TaxiDriverUser ,  c: TaxiConfirmation | t in c. camesFrom  <=> c in t. send
	}

	fact confirmationToOneSystemAnswer{
		all s: SystemAnswer ,  c: TaxiConfirmation | s in c. generates  <=> c in s. associated
	}
	
	fact confirmationUpdatesRideSchedule{
		all c:TaxiConfirmation, r:RideSchedule | r in c. updates  <=> c in r. updatedBy
	}

	fact confirmationUpdatesRightSchedule{
		all c:TaxiConfirmation | some r:RideSchedule, t:TaxiDriverUser |  (t in c. camesFrom <=> t in r. associatedTo) and  
		(r in	c.updates <=> r in t. has ) and ( t  in r. associatedTo)  
	}

//Queue Relations:

	fact eachTaxiCouldBeEnqueuedOnlyInOneQueue{
		all t: TaxiDriverUser ,  q: Queue | t in q. contains  <=> q in t. enqueuedInto
	}

	fact oneQueueForOneZone{
		all q: Queue ,  z: Zone | z in q. associatedTo  <=> q in z. haveOne
	}
	
	// A driver is removed from the queue if he send a confirmation 

	fact driverRemovedFromTheQueue{
		all t:TaxiDriverUser, q: Queue, c: TaxiConfirmation | t in c. camesFrom <=> t not in q. contains
	}

	// A Driver not in queue is not available

	fact TaxiNotInQueueISunaVailable {
		all t:TaxiDriverUser, q: Queue | t not in q. contains <=> (t.availability = NotAvailable)  and t not in q. contains
	}

	// A Driver in queue is available 

	fact TaxiNotInQueueISunaVailable {
		all t:TaxiDriverUser, q: Queue | t in q. contains <=> (t.availability = Available)
	}

//Ride Schedule Relations: 

	fact oneRideScheduleForOneDriver{
		all r: RideSchedule, t: TaxiDriverUser | r in t. has <=> t in r. associatedTo		
	}
	
//Ban Relations: 
	
	fact aBannedUserCannotSendRequest{
		all p:PassengerUser | (#p.banned = 1) implies (p.send = none)  
	}

//Sharing Relations:

	//If two request have the same origin and destination, they are sharable

	fact SharingFinding {
		all r1,r2: Request | ((r1.startsFrom = r2.startsFrom) and 
		(r1.endsIn = r2.endsIn) and not(r1.startsFrom = none) 
		and not(r1.endsIn = none)and not(r1= r2)) implies ( (#r1.sharingAvailable > 0) and 
		(#r2.sharingAvailable > 0) )
	}


pred show{

}

run show  for 4
