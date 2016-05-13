abstract sig Person{}

abstract sig Superuser{}

sig Guest extends Person{}

sig User extends Person{

		recive: set Notification,
		reserve: set ParkingReserve

}

sig Administration extends Superuser{}

sig AdminNotification{}

sig Hospital extends Superuser{}

sig Queue {}

sig Police extends Superuser{}

sig PublicTransport extends Superuser{}

sig PubTraNotification{}

sig Parking extends Superuser{}
