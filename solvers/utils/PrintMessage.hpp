#ifndef PRINTMESSAGE_HPP_
#define PRINTMESSAGE_HPP_

namespace MinisatID{
class idpexception;

namespace Print{
	void printDataInitStart(int v);
	void printDataInitEnd(int v) ;

	void printMainStart(int v);
	void printMainEnd(int v);

	void printExceptionCaught(const idpexception& e, int v);
	void printUnexpectedError(int v);
}

}

#endif /* PRINTMESSAGE_HPP_ */
