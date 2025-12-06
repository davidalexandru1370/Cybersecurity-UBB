package com.example.backend.business.entities;

import com.example.backend.core.enums.Role;

public class CreateUserDTO {
    private String email;
    private String password;
    private Role role;

    public CreateUserDTO(String username, String password, Role role) {
        this.email = username;
        this.password = password;
        this.role = role;
    }

    public String getEmail() {
        return email;
    }

    public String getPassword() {
        return password;
    }

    public Role getRole() {
        return role;
    }
}
