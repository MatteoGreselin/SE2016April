//-------SIGNATURES-------//

abstract sig Person{}

abstract sig Superuser{}

sig Guest extends Person{}

sig User extends Person{

		recive: set Notification,
		reserve: set ParkingReserve,

}

sig Administration extends Superuser{

		manageN: set FeedbackNot,
		manafeT: set TrafficLights,
		send: set AdminNotification,
		recive: set email,
		#CityAdministration = 1

}

sig AdminNotification{

		sender: one CityAdministration,
		receive: all User
}

sig Hospital extends Superuser{

		recive: set HelpRequest,
		manage: set HospitalSpecializations,
		manage: set Queue,
		#Hospital >= 1				
}

sig Queue {}

sig Police extends Superuser{

		recive: set HelpRequest;
		#Police >= 1
}

sig PublicTransport extends Superuser{

		manage: set PublicTransportPosition,
		send: set ExceptionalNotification,
		#PublicTransportCompany = 1

}

sig PublicTransportPosition{}

sig ExceptionalNotification{

		sender: one PublicTransport,
		receiver: all User

}

sig Parking extends Superuser{}

sig ParkingReservation{

		sender: one User,
		revicer: one Parking

}

//-------ASSERTIONS-------//


//-------PREDICATES-------//
