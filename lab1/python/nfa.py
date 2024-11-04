#!/usr/bin/env python

import sys
from enum import Enum
from typing import List, Optional
import re

"""
本文件中已经定义好了一些类和函数，类内也已经定义好了一些成员变量和方法。不建议大家修改这些已经定义好的东西。
但是，为了实现功能，你可以自由地增加新的函数、类等，包括可以在已经定义好的类自由地添加新的成员变量和方法。

本文件可以直接作为python的入口点文件。
支持两种运行方式：
1、将输入文件的文件名作为唯一的命令行参数传入。
   例如: python nfa.py ../cases/01.txt
2、若不传入任何参数，则程序将从stdin中读取输入。
"""
"""
在第一次实验中，保证状态转移规则的字母和输入的字符串都仅包含ASCII字符，且不包含'\0'和换行符'\r' '\n'。
第一次实验要求支持的特殊字符有：\d \w \s \D \W \S \. 
前六个的定义同一般正则表达式中的定义，最后一个\.则等同于一般正则表达式中的.，可匹配任何字符。
各个字符的具体定义可查看 https://www.runoob.com/regexp/regexp-metachar.html 
"""


class RuleType(Enum):
    """
    用于表示状态转移的类型的枚举。
    示例用法： if rule.type == RuleType.EPSILON:
    """
    NORMAL = 0  # 一般转移。如 a
    RANGE = 1  # 字符区间转移。如 a-z
    SPECIAL = 2  # 特殊转移。如 \d （注意Rule的by属性里面是没有斜杠的，只有一个字母如d）
    EPSILON = 3  # epsilon-转移。


class Rule:
    """
    表示一条状态转移规则。
    """
    dst: int  # 目的状态
    type: RuleType  # 状态转移的类型，详见RuleType的注释
    by: str = ""  # 对特殊字符转移，这里只有一个字母，如d；对字符区间转移，这里是区间的开头，如a；对一般转移，这里就是转移所需的字母；对epsilon-转移，这里固定为空串。
    to: str = ""  # 对字符区间转移，这里是区间的结尾，如z；对任何其他类型的转移，这里固定为空串。

    def match(self, c: str) -> bool:
        """
        判断当前规则是否匹配指定的字符。
        """
        if self.type == RuleType.NORMAL:
            return self.by == c
        elif self.type == RuleType.RANGE:
            return ord(self.by) <= ord(c) <= ord(self.to)
        elif self.type == RuleType.SPECIAL:
            if self.by == "d":
                # [0-9]
                return c.isdigit()
            elif self.by == "w":
                # [A-Za-z0-9_]，即字母、数字、下划线
                return c.isalnum() or c == "_"
            elif self.by == "s":
                # [ \f\n\r\t\v]
                return c.isspace()
            elif self.by == "D":
                return not c.isdigit()
            elif self.by == "W":
                return not c.isalnum() and c != "_"
            elif self.by == "S":
                return not c.isspace()
            elif self.by == ".":
                # 匹配除换⾏符 \r \n 以外的任意单个字符。
                return c != '\n' and c != '\r'
            else:
                raise ValueError("未知的特殊字符：" + self.by)
        elif self.type == RuleType.EPSILON:
            raise ValueError("epsilon转移不应该调用match函数！")
        else:
            raise ValueError("未知的规则类型：" + str(self.type))


class Path:
    """
    表示一条从初态到终态的路径。
    当输入字符串的执行结果是接受时，你需要根据接受的路径，正确构造一个该类的对象并返回。
    """
    states: List[int] = []  # 从初态到终态经历的状态列表。开头必须是0。
    consumes: List[str] = []  # 长度必须为states的长度-1。consumes[i]表示states[i]迁移到states[i+1]时所消耗的字母（若是不消耗字母的epsilon转移，则设为空串""即可）]

    def __str__(self):
        """
        将Path转为（序列化为）文本的表达格式（以便于通过stdout输出）
        你不需要理解此函数的含义、阅读此函数的实现和调用此函数。
        """
        result = ""
        if len(self.consumes) != len(self.states) - 1: raise AssertionError("Path的len(consumes)不等于len(states)-1！")
        for i in range(len(self.consumes)):
            result += str(self.states[i]) + " " + self.consumes[i] + " "
        result += str(self.states[-1])
        return result


class NFA:
    """
    表示一个NFA的类。
    本类定义的自动机，约定状态用编号0~(num_states-1)表示，初态固定为0。
    """
    num_states: int = 0  # 状态个数
    is_final: List[bool] = []  # 用于判断状态是否为终态的数组，长为num_states。is_final[i]为true表示状态i为终态。
    rules: List[List[Rule]] = []  # 表示所有状态转移规则的二维数组，长为num_states。rules[i]表示从状态i出发的所有转移规则。

    # 用于回溯路径
    def backtrace(self, path: dict) -> Path:
        """
        用于回溯路径
        :param path: 保存每一步的状态和剩余输入串
        :return: 返回找到的路径
        """
        states = []
        consumes = []
        step = max(path.keys())
        
        for i in range(step, 0, -1):
            states.append(path[i][0])
            if path[i][1] == path[i - 1][1]:
                consumes.append("")
            else:
                consumes.append(path[i - 1][1][0])
        states.append(0)
        path = Path()
        path.states = states[::-1]
        path.consumes = consumes[::-1]
        return path

    def exec(self, text: str) -> Optional[Path]:
        """
        在自动机上执行指定的输入字符串。
        :param text: 输入字符串
        :return: 若拒绝，返回None。若接受，返回一个Path类的对象。
        
         
        """
        stack = [(0, text, 0)]  # 初始化栈，包含起始状态、完整输入字符串和初始步数
        path = {}  # 用于记录每一步的状态和剩余输入串
        visited = set()  # 用于记录已经访问过的状态和对应的剩余输入字符串组合

        # TODO ε转移需要避免循环，所以需要判断是否已经走过这个状态
        while stack:  # 循环直到栈为空
            q, remaining_str, step = stack.pop()  # 从栈中取出一个元素
            path[step] = (q, remaining_str)  # 记录当前步骤的状态和剩余的输入字符串

            if self.is_final[q] and not remaining_str:  # 如果当前状态是终态且剩余输入字符串为空
                return self.backtrace(path)  # 调用backtrace函数返回找到的路径

            for rule in reversed(self.rules[q]):  # 遍历当前状态的所有转移规则
                next_state = (rule.dst, remaining_str)  # 下一个状态和剩余输入字符串
                if rule.type == RuleType.EPSILON:  # 如果是ε转移
                    if next_state not in visited:
                        stack.append((rule.dst, remaining_str, step + 1))  # 目标状态、剩余输入字符串、步数+1
                        visited.add(next_state)  # 标记为已访问
                elif remaining_str and rule.match(remaining_str[0]):  # 如果规则与当前输入字符串的第一个字符匹配
                    stack.append((rule.dst, remaining_str[1:], step + 1))  # 目标状态、去掉第一个字符的剩余输入字符串、步数+1

        return None  # 如果循环结束仍未找到接受的路径，则返回None

        
        

    @staticmethod
    def from_text(text: str) -> "NFA":
        """
        从自动机的文本表示构造自动机
        你不需要理解此函数的含义、阅读此函数的实现和调用此函数。
        """
        nfa = NFA()
        lines = text.splitlines()
        reading_rules = False
        type = ""
        for line in lines:
            if line == "": continue
            if line.startswith("type:"):
                type = line[5:].strip()
                continue
            if type != "nfa": raise ValueError("输入文件的类型不是nfa！")
            if line.startswith("states:"):
                nfa.num_states = int(line[7:])
                nfa.is_final = [False for _ in range(nfa.num_states)]
                nfa.rules = [[] for _ in range(nfa.num_states)]
                continue
            elif line.startswith("final:"):
                if nfa.num_states == 0: raise AssertionError("states必须出现在final和rules之前!")
                content = line[6:].strip()
                for s in content.split(" "):
                    if s == "": continue
                    nfa.is_final[int(s)] = True
                reading_rules = False
                continue
            elif line.startswith("rules:"):
                if nfa.num_states == 0: raise AssertionError("states必须出现在final和rules之前!")
                reading_rules = True
                continue
            elif line.startswith("input:"):
                reading_rules = False
                continue
            elif reading_rules:
                arrow_pos = line.find("->")
                space_pos = line.find(" ")
                if arrow_pos != -1 and space_pos != -1 and arrow_pos < space_pos:
                    src = int(line[0:arrow_pos])
                    dst = int(line[arrow_pos + 2:space_pos])
                    content = line[space_pos + 1:]
                    success = True
                    while success and content != "":
                        p = content.find(" ")
                        if p == -1:
                            p = len(content)
                        elif p == 0:
                            p = 1  # 当第一个字母是空格时，说明转移的字符就是空格。于是假定第二个字母也是空格（如果不是，会在后面直接报错）
                        rule = Rule()
                        rule.dst = dst
                        if p == 3 and content[1] == '-':
                            rule.type = RuleType.RANGE
                            rule.by = content[0]
                            rule.to = content[2]
                        elif p == 2 and content[0] == "\\":
                            if content[1] == "e":
                                rule.type = RuleType.EPSILON
                            else:
                                rule.type = RuleType.SPECIAL
                                rule.by = content[1]
                        elif p == 1 and (p >= len(content) or content[p] == ' '):
                            rule.type = RuleType.NORMAL
                            rule.by = content[0]
                        else:
                            success = False
                        nfa.rules[src].append(rule)
                        content = content[p + 1:]
                    if success:
                        continue
        return nfa


if __name__ == '__main__':
    """
    程序入口点函数。已经帮你封装好了读取文本输入、构造自动机并执行字符串、输出结果等。
    一般来说，你不需要阅读和改动这里的代码，只需要完成exec函数即可。
    """
    if len(sys.argv) >= 2:
        with open(sys.argv[1], "r") as f:
            text = f.read()
    else:
        text = sys.stdin.read()

    input_str = None
    lines = text.splitlines()
    for line in lines:
        if line.startswith("input: "): input_str = line[7:]
    if input_str is None:
        raise ValueError("未找到输入字符串！注意输入字符串必须以input: 开头，其中冒号后面必须有空格！")

    nfa = NFA.from_text(text)
    result = nfa.exec(input_str)
    if result is None:
        print("Reject", end='')
    else:
        print(str(result), end='')
