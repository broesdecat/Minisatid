#ifndef LAZYCLAUSESUPPORT_HPP_
#define LAZYCLAUSESUPPORT_HPP_

#include "callback.hpp"

#include "external/Datastructures.hpp"

namespace MinisatID {

class LazyGroundingCommand {
private:
	bool allreadyground;
public:
	LazyGroundingCommand()
			: allreadyground(false) {
	}
	virtual ~LazyGroundingCommand() {
	}

	virtual void requestGrounding() = 0;

	void notifyGrounded() {
		allreadyground = true;
	}
	bool isAlreadyGround() const {
		return allreadyground;
	}
};

// POCO
class LazyGroundLit {
public:
	bool watchboth;
	Literal residual;
	LazyGroundingCommand* monitor;

	LazyGroundLit(bool watchboth, const Literal& residual, LazyGroundingCommand* monitor)
			: watchboth(watchboth), residual(residual), monitor(monitor) {
	}
};

}

#endif /* LAZYCLAUSESUPPORT_HPP_ */
