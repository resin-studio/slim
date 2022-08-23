from typing import TypeVar
T = TypeVar('T')

class D:
    @staticmethod
    def foo(x : T) -> T:
        return x 
    
# ALL T . T -> T 
def foo(x : T) -> T:
    return x 


def boo(x : D) -> D:
    return x 
