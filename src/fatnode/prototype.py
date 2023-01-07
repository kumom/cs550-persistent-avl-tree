from typing import Any

class Entry:
    def __init__(self):
        self.roots = [None]
        self.time = 0

    def get(self, version):
        if len(self.roots) > version:
            return self.roots[version]
        else:
            return self.roots[-1]

    def insert(self, value):
        self.time += 1
        root = self.roots[-1]
        if root is None:
            self.roots += [Node(value, self.time)]
        else:
            inserted = root.insert(value, self.time)
            if inserted is False:
                self.time -= 1
            else:
                self.roots += [root]

    def delete(self, value):
        if self.roots[-1] is not None:
            root = self.roots[-1]
            self.time += 1
            newRoot = root.delete(None, value, self.time)
            if newRoot:
                self.roots += [newRoot]
            else:
                self.roots += [root]

    def find(self, version, value):
        if len(self.roots) > version:
            root = self.roots[version]
        else:
            root = self.roots[-1]

        if root:
            return root.find(version, value)
        else:
            return False

class Node:
    def __init__(self, value: int, time: int):
        self.values: list[tuple[int, int]] = [(time, value)]
        self.rights: list[tuple[int, Any]] = []
        self.lefts: list[tuple[int, Any]] = []

    def __repr__(self):
        values = list(map(lambda x: f'value {x[0]}: {x[1]}', self.values))
        lefts = list(map(lambda x: f'left {x[0]}: {x[1]}', self.lefts))
        rights = list(map(lambda x: f'right {x[0]}: {x[1]}', self.rights))
        all = list(map(lambda x: x, lefts + values + rights))
        return str(all)

    def left(self):
        if len(self.lefts) > 0:
            return self.lefts[-1][1]
        else:
            return None

    def right(self):
        if len(self.rights) > 0:
            return self.rights[-1][1]
        else:
            return None

    def value(self):
        return self.values[-1][1]

    def insert(self, value, time) -> bool:
        x = self.value()
        if x < value:
            right = self.right()
            if right is None:
                self.rights += [(time, Node(value, time))]
                return True
            else:
                return right.insert(value, time)
        elif x > value:
            left = self.left()
            if left is None:
                self.lefts += [(time, Node(value, time))]
                return True
            else:
                return left.insert(value,  time)

        return False
    
    def deleteMin(self, parent, time):
        left = self.left()
        if left is None:
            parent.lefts += [(time, None)]
            return (self.value(), self.right())
        else:
            return left.deleteMin(self, time)

    def delete(self, parent, value: int, time) -> Any:
        x = self.value()
        right = self.right()
        left = self.left()
        if x == value:
            newNode = None
            if right is not None:
                (minV, node) = right.deleteMin(right, time)
                newNode = node
                self.values += [(time, minV)]
                self.rights += [(time, node)]
            else:
                newNode = left

            if parent is None:
                return newNode
            else:
                if parent.left == self:
                    parent.lefts += [(time, newNode)]
                else:
                    parent.rights += [(time, newNode)]

        elif x < value:
            if right is None:
                return None
            else:
                return right.delete(self, value, time)
        else:
            if left is None:
                return None
            else:
                return left.delete(self, value, time)

    def findHelper(self, version: int, fieldName: str) -> Any:
        if version < self.values[0][0]:
            return None

        if (fieldName == "value"):
            arr = self.values
        elif (fieldName == "right"):
            arr = self.rights
        elif (fieldName == "left"):
            arr = self.lefts
        else:
            return None
            
        if len(arr) == 0:
            return None

        lo, hi = 0, len(arr) - 1
        i = 0
        while lo <= hi:
            mid = lo + (hi - lo) // 2
            (v, x) = arr[mid]
            if version >= v:
                i = mid
                lo = mid + 1
                if version == v:
                    break
            else:
                hi = mid - 1

        return arr[i][1]

    def find(self, version: int, value: int):
        x = self.findHelper(version, 'value')
        if x is None:
            return False
        else:
            if x > value:
                left = self.findHelper(version, 'left')
                if left == None:
                    return False
                else:
                    return left.find(version, value)
            elif x < value:
                right = self.findHelper(version, 'right')
                if right == None:
                    return False
                else:
                    return right.find(version, value)
            else:
                return True


entry = Entry() 
entry.insert(1) #1
entry.delete(1) #2
entry.insert(3) #3
entry.insert(2) #4
entry.insert(4) #5
entry.insert(6) #6
entry.insert(6) #6
print(entry.get(8))
entry.delete(3) #7
print(entry.get(8))
entry.insert(6) #8
entry.insert(7) #9



for i in range(0, 10):
    print(f'At time {i}:')
    print(entry.find(i, 3))
    print("--------")
