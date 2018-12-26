from bls12381 import q as order
from fields import Fq
from ec import hash_to_point_Fq


fq_0 = Fq.zero(order)
fq_1 = Fq.one(order)

fq_elems = [fq_0]*16

fq_elems[0] = fq_1
for i in range(1, 16):
    fq_elems[i] = fq_elems[i-1] + fq_1


to_bls12_elem = lambda e: Fq(order, e)


class Sharkmimc:
    def __init__(self, num_branches=4, middle_rounds=38):
        self.num_branches = num_branches
        self.middle_rounds = middle_rounds
        self.total_rounds = 6 + middle_rounds
        self.round_keys = []
        self.round_constants = []
        self.matrix_1 = []
        self.matrix_2 = []
        self.gen_matrix_1()
        self.gen_matrix_2()
        self.gen_round_constants()
        self.gen_round_keys()

    def gen_matrix_1(self):
        self.matrix_1 = [[fq_1]*self.num_branches]*self.num_branches

    def gen_matrix_2(self):
        self.matrix_2 = [[fq_1]*self.num_branches]*self.num_branches

    def gen_round_constants(self):
        for _ in range(self.total_rounds * self.num_branches):
            self.round_constants.append(fq_1)

    def gen_round_keys(self):
        for _ in range((self.total_rounds + 1) * self.num_branches):
            self.round_keys.append(fq_1)

    @staticmethod
    def apply_sbox(elem):
        raise NotImplementedError

    def hash(self, input):
        assert len(input) == self.num_branches

        value_branch = [to_bls12_elem(i) for i in input]
        value_branch_temp = [fq_0] * self.num_branches

        round_keys_offset = 0

        for _ in range(3):
            for i in range(self.num_branches):
                value_branch[i] = value_branch[i] + self.round_keys[round_keys_offset]
                value_branch[i] = self.apply_sbox(value_branch[i])
                round_keys_offset += 1

            for j in range(self.num_branches):
                for i in range(self.num_branches):
                    temp = self.matrix_2[i][j] * value_branch[j]
                    value_branch_temp[i] += temp

            value_branch = value_branch_temp[:]
            value_branch_temp = [fq_0] * self.num_branches

        for _ in range(self.middle_rounds):
            for i in range(self.num_branches):
                value_branch[i] = value_branch[i] + self.round_keys[round_keys_offset]
                round_keys_offset += 1

            value_branch[0] = self.apply_sbox(value_branch[0])

            for j in range(self.num_branches):
                for i in range(self.num_branches):
                    temp = self.matrix_2[i][j] * value_branch[j]
                    value_branch_temp[i] += temp

            value_branch = value_branch_temp[:]
            value_branch_temp = [fq_0] * self.num_branches

        for _ in range(2):
            for i in range(self.num_branches):
                value_branch[i] = value_branch[i] + self.round_keys[round_keys_offset]
                value_branch[i] = self.apply_sbox(value_branch[i])
                round_keys_offset += 1

            for j in range(self.num_branches):
                for i in range(self.num_branches):
                    temp = self.matrix_2[i][j] * value_branch[j]
                    value_branch_temp[i] += temp

            value_branch = value_branch_temp[:]

        for i in range(self.num_branches):
            value_branch[i] = value_branch[i] + self.round_keys[round_keys_offset]
            value_branch[i] = self.apply_sbox(value_branch[i])
            round_keys_offset += 1

            value_branch[i] = value_branch[i] + self.round_keys[round_keys_offset]
            round_keys_offset += 1

        return value_branch


class SharkmimcCube(Sharkmimc):
    @staticmethod
    def apply_sbox(elem):
        return elem * elem * elem


class SharkmimcInverse(Sharkmimc):
    @staticmethod
    def apply_sbox(elem):
        return elem.__invert__()


if __name__== "__main__":
    h1 = hash_to_point_Fq('1')
    h2 = hash_to_point_Fq('2')

    # input = [h1.x, h1.y, h2.x, h2.y]
    input = [1, 2, 3, 4]
    print('Input >>>>>>>>>')
    print(input)
    print([to_bls12_elem(i) for i in input])

    print('Output when Sbox is Cube >>>>>>>>>')
    hf_cube = SharkmimcCube()
    print('Hex:', hf_cube.hash(input))
    print('Decimal:', list(map(int, hf_cube.hash(input))))

    print('Output when Sbox is Inverse >>>>>>>>>')
    hf_inv = SharkmimcInverse()
    print('Hex:', hf_inv.hash(input))
    print('Decimal:', list(map(int, hf_inv.hash(input))))
