fn decimal_to_binary(decimal: u128) -> String {
    let mut num = decimal;
    let mut binary = String::new();

    if num == 0 {
        binary.push('0');
    }

    while num > 0 {
        let bit = num % 2;
        binary = format!("{}{}", bit, binary);
        num /= 2;
    }

    binary
}

pub fn bitwise_and(decimal1: u128, decimal2: u128) -> u128 {
    let binary1 = decimal_to_binary(decimal1);
    let binary2 = decimal_to_binary(decimal2);

    let mut result = 0;

    // Convert binary strings to vectors of characters for easier manipulation
    let binary_chars1: Vec<char> = binary1.chars().collect();
    let binary_chars2: Vec<char> = binary2.chars().collect();

    // Perform bitwise AND operation
    for i in 0..binary_chars1.len().max(binary_chars2.len()) {
        let bit1 = if i < binary_chars1.len() {
            binary_chars1[i]
        } else {
            '0'
        };

        let bit2 = if i < binary_chars2.len() {
            binary_chars2[i]
        } else {
            '0'
        };

        if bit1 == '1' && bit2 == '1' {
            result += 2u128.pow((binary_chars1.len().max(binary_chars2.len()) - 1 - i) as u32);
        }
    }

    result
}
